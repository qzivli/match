(library (edu indiana match)
  (export match trace-match
          match+ trace-match+
          match/lexical-context trace-match/lexical-context
          match-equality-test
          guard ... quasiquote unquote unquote-splicing ->)
  (import (rnrs)
          (rnrs mutable-pairs)
          (edu indiana compat))

  (define-syntax ->
    (lambda (x)
      (syntax-violation #f "misplaced aux keyword" x)))

  (define match-equality-test
    (make-parameter
        equal?
      (lambda (x)
        (unless (procedure? x)
          (error 'match-equality-test "not a procedure" x))
        x)))

  (define-syntax match+
    (lambda (x)
      (syntax-case x ()
        ((ctxt (ThreadedId ...) Exp Clause ...)
         #'(let f ((ThreadedId ThreadedId) ... (x Exp))
             (match-help ctxt f x (ThreadedId ...) Clause ...))))))


  (define-syntax match/lexical-context
    (lambda (x)
      (syntax-case x ()
        ((_ ctxt Exp Clause ...)
         #'(let f ((x Exp))
             (match-help ctxt f x () Clause ...))))))

  (define-syntax match
    (lambda (x)
      (syntax-case x ()
        ((ctxt Exp Clause ...)
         #'(match/lexical-context ctxt Exp Clause ...)))))

  (define-syntax trace-match+
    (lambda (x)
      (syntax-case x ()
        ((ctxt (ThreadedId ...) Name Exp Clause ...)
         #'(letrec ((f (trace-lambda Name (ThreadedId ... x)
                         (match-help ctxt f x (ThreadedId ...) Clause ...))))
             (f ThreadedId ... Exp))))))

  (define-syntax trace-match/lexical-context
    (lambda (x)
      (syntax-case x ()
        ((_ ctxt Name Exp Clause ...)
         #'(letrec ((f (trace-lambda Name (x)
                         (match-help ctxt f x () Clause ...))))
             (f Exp))))))

  (define-syntax trace-match
    (lambda (x)
      (syntax-case x ()
        ((ctxt Name Exp Clause ...)
         #'(trace-match/lexical-context ctxt Name Exp Clause ...)))))

  ;; ------------------------------

  (define-syntax let-values**
    (syntax-rules ()
      ((_ () B0 B ...) (begin B0 B ...))
      ((_ ((Formals Exp) Rest ...) B0 B ...)
       (let-values** (Rest ...)
                     (call-with-values (lambda () Exp)
                       (lambda Formals B0 B ...))))))

  (define-syntax match-help
    (lambda (x)
      (syntax-case x ()
        ((_ Template Cata Obj ThreadedIds)
         #'(error 'match "Unmatched datum" Obj))
        ((_ Template Cata Obj ThreadedIds (Pat B0 B ...) Rest ...)
         #'(convert-pat Pat
                        (match-help1 Template Cata Obj ThreadedIds
                                     (B0 B ...)
                                     Rest ...))))))

  (define-syntax match-help1
    (lambda (x)
      (syntax-case x (guard)
        ((_ PatLit Vars () Cdecls Template Cata Obj ThreadedIds
            ((guard) B0 B ...) Rest ...)
         #'(let ((ls/false (sexp-dispatch Obj PatLit)))
             (if ls/false
                 (apply (lambda Vars
                          (clause-body Cata Cdecls ThreadedIds
                                       (extend-backquote Template B0 B ...)))
                        ls/false)
                 (match-help Template Cata Obj ThreadedIds Rest ...))))
        ((_ PatLit Vars (PG ...) Cdecls Template Cata Obj ThreadedIds
            ((guard G ...) B0 B ...) Rest ...)
         #'(let ((ls/false (sexp-dispatch Obj PatLit)))
             (if (and ls/false (apply (lambda Vars
                                        (guard-body Cdecls
                                                    (extend-backquote Template
                                                                      (and PG ... G ...))))
                                      ls/false))
                 (apply (lambda Vars
                          (clause-body Cata Cdecls ThreadedIds
                                       (extend-backquote Template B0 B ...)))
                        ls/false)
                 (match-help Template Cata Obj ThreadedIds Rest ...))))
        ((_ PatLit Vars (PG ...) Cdecls Template Cata Obj ThreadedIds
            (B0 B ...) Rest ...)
         #'(match-help1 PatLit Vars (PG ...) Cdecls Template Cata Obj ThreadedIds
                        ((guard) B0 B ...) Rest ...)))))

  (define-syntax clause-body
    (lambda (x)
      (define build-mapper
        (lambda (vars depth cata tIds)
          (if (zero? depth)
              cata
              (with-syntax ((rest (build-mapper vars (- depth 1) cata tIds))
                            (vars vars)
                            (tIds tIds))
                  #'(mapper rest vars tIds)))))
      (syntax-case x ()
        ((_ Cata ((CVar CDepth CMyCata CFormal ...) ...) (ThreadedId ...) B)
         (with-syntax (((Mapper ...)
                        (map (lambda (mycata formals depth)
                               (build-mapper formals
                                             (syntax->datum depth)
                                             (syntax-case mycata ()
                                               (#f #'Cata)
                                               (exp #'exp))
                                             #'(ThreadedId ...)))
                             #'(CMyCata ...)
                             #'((CFormal ...) ...)
                             #'(CDepth ...))))
             #'(let-values** (((ThreadedId ... CFormal ...)
                               (Mapper ThreadedId ... CVar))
                              ...)
                             B))))))

  (define-syntax guard-body
    (lambda (x)
      (syntax-case x ()
        ((_ ((Cvar Cdepth MyCata Cformal ...) ...) B)
         (with-syntax (((CF ...) (apply append #'((Cformal ...) ...))))
             #'(let-syntax
                   ((CF
                     (lambda (x)
                       (syntax-case x ()
                         (Name
                          (syntax-error #'Name
                                        "guard cannot refer to return-value variable")))))
                    ...)
                 B))))))

  (define-syntax convert-pat
    ;; returns sexp-pat x vars x guards x cdecls
    (let ()
      (define ellipsis?
        (lambda (x)
          (and (identifier? x) (free-identifier=? x #'(... ...)))))
      (define Var?
        (lambda (x)
          (syntax-case x (->)
            (-> #f)
            (id (identifier? #'id)))))
      (define fVar
        (lambda (var vars guards)
          (let loop ((ls vars))
            (if (null? ls)
                (values (cons var vars) guards)
                (if (bound-identifier=? var (car ls))
                    (with-syntax (((tmp) (generate-temporaries (list var)))
                                  (var (car ls)))
                        (values (cons #'tmp vars)
                                (cons #'((match-equality-test) tmp var) guards)))
                    (loop (cdr ls)))))))
      (define (f syn vars guards cdecls depth)
        (define (andmap f ls)
          (cond
           ((null? ls) #t)
           ((null? (cdr ls)) (f (car ls)))
           (else (and (f (car ls)) (andmap f (cdr ls))))))
        (syntax-case syn (unquote)
          ((unquote . stuff) ; separate for better error detection
           (syntax-case syn (unquote ->)
             ((unquote (MyCata -> Var ...))
              (andmap Var? #'(Var ...))
              (with-syntax (((Temp) (generate-temporaries '(x)))
                            (Depth depth))
                  (values #'any
                          (cons #'Temp vars)
                          guards
                          (cons #'(Temp Depth MyCata Var ...) cdecls))))
             ((unquote (Var ...))
              (andmap Var? #'(Var ...))
              (with-syntax (((Temp) (generate-temporaries '(x)))
                            (Depth depth))
                  (values #'any
                          (cons #'Temp vars)
                          guards
                          (cons #'(Temp Depth #f Var ...) cdecls))))
             ((unquote Var)
              (Var? #'Var)
              (let-values* (((vars guards) (fVar #'Var vars guards)))
                           (values #'any vars guards cdecls)))))
          (((unquote . stuff) Dots)
           (ellipsis? #'Dots)
           (syntax-case syn (unquote ->)
             (((unquote (MyCata -> Var ...)) Dots)
              (andmap Var? #'(Var ...))
              (with-syntax (((Temp) (generate-temporaries '(x)))
                            (Depth+1 (add1 depth)))
                  (values #'each-any
                          (cons #'Temp vars)
                          guards
                          (cons #'(Temp Depth+1 MyCata Var ...) cdecls))))
             (((unquote (Var ...)) Dots)
              (andmap Var? #'(Var ...))
              (with-syntax (((Temp) (generate-temporaries '(x)))
                            (Depth+1 (add1 depth)))
                  (values #'each-any
                          (cons #'Temp vars)
                          guards
                          (cons #'(Temp Depth+1 #f Var ...) cdecls))))
             (((unquote Var) Dots)
              (Var? #'Var)
              (let-values* (((vars guards) (fVar #'Var vars guards)))
                           (values #'each-any vars guards cdecls)))
             ((expr Dots) (syntax-error #'expr "match-pattern unquote syntax"))))
          ((Pat Dots)
           (ellipsis? #'Dots)
           (let-values* (((Dpat Dvars Dguards Dcdecls)
                          (f #'Pat vars guards cdecls (add1 depth))))
                        (with-syntax ((Size (- (length Dvars) (length vars)))
                                      (Dpat Dpat))
                            (values #'#(each Dpat Size) Dvars Dguards Dcdecls))))
          ((Pat Dots . Rest)
           (ellipsis? #'Dots)
           (let-values* (((Rpat Rvars Rguards Rcdecls)
                          (f #'Rest vars guards cdecls depth))
                         ((Dpat Dvars Dguards Dcdecls)
                          (f #'(Pat (... ...)) Rvars Rguards Rcdecls depth)))
                        (with-syntax ((Size (- (length Dvars) (length Rvars)))
                                      ((RevRestTl . RevRest) (reverseX Rpat '()))
                                      (Dpat Dpat))
                            (values #'#(tail-each Dpat Size RevRest RevRestTl)
                                    Dvars Dguards Dcdecls))))
          ((X . Y)
           (let-values* (((Ypat Yvars Yguards Ycdecls)
                          (f #'Y vars guards cdecls depth))
                         ((Xpat Xvars Xguards Xcdecls)
                          (f #'X Yvars Yguards Ycdecls depth)))
                        (with-syntax ((Xpat Xpat) (Ypat Ypat))
                            (values #'(Xpat . Ypat) Xvars Xguards Xcdecls))))
          (() (values #'() vars guards cdecls))
          (#(X ...)
           (let-values* (((Pat Vars Eqvars Cdecls)
                          (f #'(X ...) vars guards cdecls depth)))
                        (with-syntax ((Pat Pat))
                            (values #'#(vector Pat) Vars Eqvars Cdecls))))
          (Thing (values #'#(atom Thing) vars guards cdecls))))
      (define reverseX
        (lambda (ls acc)
          (if (pair? ls)
              (reverseX (cdr ls) (cons (car ls) acc))
              (cons ls acc))))
      (define-syntax let-values*
        (syntax-rules ()
          ((_ () B0 B ...) (begin B0 B ...))
          ((_ (((Formal ...) Exp) Decl ...) B0 B ...)
           (call-with-values (lambda () Exp)
             (lambda (Formal ...)
               (let-values* (Decl ...) B0 B ...))))))
      (define-syntax let-synvalues*
        (syntax-rules ()
          ((_ () B0 B ...) (begin B0 B ...))
          ((_ (((Formal ...) Exp) Decl ...) B0 B ...)
           (call-with-values (lambda () Exp)
             (lambda (Formal ...)
               (with-syntax ((Formal Formal) ...)
                   (let-synvalues* (Decl ...) B0 B ...)))))))
      (lambda (syn)
        (syntax-case syn ()
          ((_ syn (kh . kt))
           (let-synvalues* (((Pat Vars Guards Cdecls) (f #'syn '() '() '() 0)))
                           #'(kh 'Pat Vars Guards Cdecls . kt)))))))

  (define-syntax mapper
    (lambda (x)
      (syntax-case x ()
        ((_ F (RetId ...) (ThreadId ...))
         (with-syntax (((t ...) (generate-temporaries #'(RetId ...)))
                       ((ts ...) (generate-temporaries #'(RetId ...)))
                       ((null ...) (map (lambda (x) #''()) #'(RetId ...))))
             #'(let ((fun F))
                 (letrec
                     ((g (lambda (ThreadId ... ls)
                           (if (null? ls)
                               (values ThreadId ... null ...)
                               (call-with-values
                                   (lambda () (g ThreadId ... (cdr ls)))
                                 (lambda (ThreadId ... ts ...)
                                   (call-with-values
                                       (lambda () (fun ThreadId ... (car ls)))
                                     (lambda (ThreadId ... t ...)
                                       (values ThreadId ... (cons t ts) ...)))))))))
                   g)))))))

  ;; ------------------------------

  (define-syntax my-backquote
    (lambda (x)
      (define ellipsis?
        (lambda (x)
          (and (identifier? x) (free-identifier=? x #'(... ...)))))
      (define-syntax with-values
        (syntax-rules ()
          ((_ P C) (call-with-values (lambda () P) C))))
      (define-syntax syntax-lambda
        (lambda (x)
          (syntax-case x ()
            ((_ (Pat ...) Body0 Body ...)
             (with-syntax (((X ...) (generate-temporaries #'(Pat ...))))
                 #'(lambda (X ...)
                     (with-syntax ((Pat X) ...)
                         Body0 Body ...)))))))
      (define-syntax with-temp
        (syntax-rules ()
          ((_ V Body0 Body ...)
           (with-syntax (((V) (generate-temporaries '(x))))
               Body0 Body ...))))
      (define-syntax with-temps
        (syntax-rules ()
          ((_ (V ...) (Exp ...) Body0 Body ...)
           (with-syntax (((V ...) (generate-temporaries #'(Exp ...))))
               Body0 Body ...))))
      (define destruct
        (lambda (Orig x depth)
          (syntax-case x (quasiquote unquote unquote-splicing)
            ;; inner quasiquote
            ((quasiquote Exp)
             (with-values (destruct Orig #'Exp (add1 depth))
               (syntax-lambda (Builder Vars Exps)
                              (if (null? #'Vars)
                                  (values #''(quasiquote Exp) '() '())
                                  (values #'(list 'quasiquote Builder) #'Vars #'Exps)))))
            ;; unquote
            ((unquote Exp)
             (zero? depth)
             (with-temp X
                        (values #'X (list #'X) (list #'Exp))))
            ((unquote Exp)
             (with-values (destruct Orig #'Exp (sub1 depth))
               (syntax-lambda (Builder Vars Exps)
                              (if (null? #'Vars)
                                  (values #''(unquote Exp) '() '())
                                  (values #'(list 'unquote Builder) #'Vars #'Exps)))))
            ;; splicing
            (((unquote-splicing Exp))
             (zero? depth)
             (with-temp X
                        (values #'X (list #'X) (list #'Exp))))
            (((unquote-splicing Exp ...))
             (zero? depth)
             (with-temps (X ...) (Exp ...)
                         (values #'(append X ...) #'(X ...) #'(Exp ...))))
            (((unquote-splicing Exp ...) . Rest)
             (zero? depth)
             (with-values (destruct Orig #'Rest depth)
               (syntax-lambda (Builder Vars Exps)
                              (with-temps (X ...) (Exp ...)
                                          (if (null? #'Vars)
                                              (values #'(append X ... 'Rest)
                                                      #'(X ...) #'(Exp ...))
                                              (values #'(append X ... Builder)
                                                      #'(X ... . Vars) #'(Exp ... . Exps)))))))
            ((unquote-splicing Exp ...)
             (with-values (destruct Orig #'(Exp ...) (sub1 depth))
               (syntax-lambda (Builder Vars Exps)
                              (if (null? #'Vars)
                                  (values #''(unquote-splicing Exp ...) '() '())
                                  (values #'(cons 'unquote-splicing Builder)
                                          #'Vars #'Exps)))))
            ;; dots
            (((unquote Exp) Dots)
             (and (zero? depth) (ellipsis? #'Dots))
             (with-temp X
                        (values #'X (list #'X) (list #'Exp))))
            (((unquote Exp) Dots . Rest)
             (and (zero? depth) (ellipsis? #'Dots))
             (with-values (destruct Orig #'Rest depth)
               (syntax-lambda (RestBuilder RestVars RestExps)
                              (with-syntax ((TailExp
                                             (if (null? #'RestVars)
                                                 #''Rest
                                                 #'RestBuilder)))
                                  (with-temp X
                                             (values #'(append X TailExp)
                                                     (cons #'X #'RestVars)
                                                     (cons #'Exp #'RestExps)))))))
            ((Exp Dots . Rest)
             (and (zero? depth) (ellipsis? #'Dots))
             (with-values (destruct Orig #'Exp depth)
               (syntax-lambda (ExpBuilder (ExpVar ...) (ExpExp ...))
                              (if (null? #'(ExpVar ...))
                                  (syntax-error Orig "Bad ellipsis")
                                  (with-values (destruct Orig #'Rest depth)
                                    (syntax-lambda (RestBuilder RestVars RestExps)
                                                   (with-syntax ((TailExp
                                                                  (if (null? #'RestVars)
                                                                      #''Rest
                                                                      #'RestBuilder))
                                                                 (Orig Orig))
                                                       (values #'(let f ((ExpVar ExpVar) ...)
                                                                   (if (and (pair? ExpVar) ...)
                                                                       (cons
                                                                        (let ((ExpVar (car ExpVar)) ...)
                                                                          ExpBuilder)
                                                                        (f (cdr ExpVar) ...))
                                                                       (if (and (null? ExpVar) ...)
                                                                           TailExp
                                                                           (error 'unquote
                                                                                  "Mismatched lists"
                                                                                  Orig))))
                                                               (append #'(ExpVar ...) #'RestVars)
                                                               (append #'(ExpExp ...) #'RestExps)))))))))
            ;; Vectors
            (#(X ...)
             (with-values (destruct Orig #'(X ...) depth)
               (syntax-lambda (LsBuilder LsVars LsExps)
                              (values #'(list->vector LsBuilder) #'LsVars #'LsExps))))
            ;; random stuff
            ((Hd . Tl)
             (with-values (destruct Orig #'Hd depth)
               (syntax-lambda (HdBuilder HdVars HdExps)
                              (with-values (destruct Orig #'Tl depth)
                                (syntax-lambda (TlBuilder TlVars TlExps)
                                               (with-syntax ((Hd (if (null? #'HdVars)
                                                                     #''Hd
                                                                     #'HdBuilder))
                                                             (Tl (if (null? #'TlVars)
                                                                     #''Tl
                                                                     #'TlBuilder)))
                                                   (values #'(cons Hd Tl)
                                                           (append #'HdVars #'TlVars)
                                                           (append #'HdExps #'TlExps))))))))
            (OtherThing
             (values #''OtherThing '() '())))))
      ;; macro begins
      (syntax-case x ()
        ((_ Datum)
         (with-values (destruct #'(quasiquote Datum) #'Datum 0)
           (syntax-lambda (Builder (Var ...) (Exp ...))
                          (if (null? #'(Var ...))
                              #''Datum
                              #'(let ((Var Exp) ...)
                                  Builder))))))))

  (define-syntax extend-backquote
    (lambda (x)
      (syntax-case x ()
        ((_ Template Exp ...)
         (with-syntax ((quasiquote
                        (datum->syntax #'Template 'quasiquote)))
             #'(let-syntax ((quasiquote
                             (lambda (x)
                               (syntax-case x ()
                                 ((_ Foo) #'(my-backquote Foo))))))
                 Exp ...))))))

  ;; ------------------------------

  (define-syntax with-values
    (syntax-rules ()
      ((_ P C) (call-with-values (lambda () P) C))))

  (define-syntax letcc
    (syntax-rules ()
      ((_ V B0 B ...) (call/cc (lambda (V) B0 B ...)))))

  (define classify-list
    (lambda (ls)
      (cond
       ((null? ls) 'proper)
       ((not (pair? ls)) 'improper)
       (else
        (let f ((tortoise ls) (hare (cdr ls)))
          (cond
           ((eq? tortoise hare) 'infinite)
           ((null? hare) 'proper)
           ((not (pair? hare)) 'improper)
           (else
            (let ((hare (cdr hare)))
              (cond
               ((null? hare) 'proper)
               ((not (pair? hare)) 'improper)
               (else (f (cdr ls) (cdr hare))))))))))))

  (define ilist-copy-flat
    (lambda (ils)
      (let f ((tortoise ils) (hare (cdr ils)))
        (if (eq? tortoise hare)
            (list (car tortoise))
            (cons (car tortoise) (f (cdr tortoise) (cddr hare)))))))

  (define sexp-dispatch
    (lambda (obj pat);; #f or list of vars
      (letcc escape
             (let ((fail (lambda () (escape #f))))
               (let f ((pat pat) (obj obj) (vals '()))
                 (cond
                  ((eq? pat 'any)
                   (cons obj vals))
                  ((eq? pat 'each-any)
                   ;; handle infinities
                   (case (classify-list obj)
                     ((proper infinite) (cons obj vals))
                     ((improper) (fail))))
                  ((pair? pat)
                   (if (pair? obj)
                       (f (car pat) (car obj) (f (cdr pat) (cdr obj) vals))
                       (fail)))
                  ((vector? pat)
                   (case (vector-ref pat 0)
                     ((atom)
                      (let ((a (vector-ref pat 1)))
                        (if (eqv? obj a)
                            vals
                            (fail))))
                     ((vector)
                      (if (vector? obj)
                          (let ((vec-pat (vector-ref pat 1)))
                            (f vec-pat (vector->list obj) vals))
                          (fail)))
                     ((each)
                      ;; if infinite, copy the list as flat, then do the matching,
                      ;; then do some set-cdrs.
                      (let ((each-pat (vector-ref pat 1))
                            (each-size (vector-ref pat 2)))
                        (case (classify-list obj)
                          ((improper) (fail))
                          ((infinite)
                           (let ((each-vals (f pat (ilist-copy-flat obj) '())))
                             (for-each (lambda (x) (set-cdr! (last-pair x) x))
                                       each-vals)
                             (append each-vals vals)))
                          ((proper)
                           (append
                            (let g ((obj obj))
                              (if (null? obj)
                                  (make-list each-size '())
                                  (let ((hd-vals (f each-pat (car obj) '()))
                                        (tl-vals (g (cdr obj))))
                                    (map cons hd-vals tl-vals))))
                            vals)))))
                     ((tail-each)
                      (let ((each-pat (vector-ref pat 1))
                            (each-size (vector-ref pat 2))
                            (revtail-pat (vector-ref pat 3))
                            (revtail-tail-pat (vector-ref pat 4)))
                        (when (eq? (classify-list obj) 'infinite) (fail))
                        (with-values
                            (let g ((obj obj))
                              ;; in-tail?, vals, revtail-left/ls
                              (cond
                               ((pair? obj)
                                (with-values (g (cdr obj))
                                  (lambda (in-tail? vals tail-left/ls)
                                    (if in-tail?
                                        (if (null? tail-left/ls)
                                            (values #f vals (list (car obj)))
                                            (values #t (f (car tail-left/ls)
                                                          (car obj)
                                                          vals)
                                                    (cdr tail-left/ls)))
                                        (values #f vals
                                                (cons (car obj) tail-left/ls))))))
                               (else
                                (values #t
                                        (f revtail-tail-pat obj vals)
                                        revtail-pat))))
                          (lambda (in-tail? vals tail-left/ls)
                            (if in-tail?
                                (if (null? tail-left/ls)
                                    (append (make-list each-size '())
                                            vals)
                                    (fail))
                                (f each-pat tail-left/ls vals))))))))
                  (else
                   (if (eqv? obj pat)
                       vals
                       (fail)))))))))
  ) ; end of library
