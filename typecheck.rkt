#lang plait

(require "class.rkt"
         "inherit.rkt"
         "types.rkt"
         "utils.rkt")

(module+ test
  (print-only-errors #t))

;; --------typecheck an expression-----------

(define typecheck-expr : (ExpI ClassList Type T-Env InterfList -> Type)
  (lambda (expr t-classes this-type tenv interfs)
    (local [(define (recur expr)
              (typecheck-expr expr t-classes this-type tenv interfs))
            (define (recur-with with-env expr)
              (typecheck-expr expr t-classes this-type with-env interfs))
            (define (typecheck-nums l r)
              (type-case Type (recur l)
                [(numT)
                 (type-case Type (recur r)
                   [(numT) (numT)]
                   [else (type-error r "num")])]
                [else (type-error l "num")]))]
      (type-case ExpI expr
        [(numI n) (numT)]
        [(idI s) (rethrow (find tenv s)
                          'typecheck
                          (string-append "not found: id "
                                         (to-string s)))]
        [(plusI l r) (typecheck-nums l r)]
        [(multI l r) (typecheck-nums l r)]
        [(thisI) this-type]
        [(newI class-name exprs)
         (local [(define arg-types (map recur exprs))
                 (define field-types
                   (get-all-field-types class-name t-classes))]
           (if (and (= (length arg-types) (length field-types))
                    (foldl2
                     (lambda (arg-t field-t acc)
                       (and acc
                            (is-subtype? arg-t field-t t-classes interfs)))
                     #t
                     arg-types
                     field-types))
               (objT class-name)
               (type-error expr "field type mismatch")))]
        [(getI obj-expr field-name)
         (type-case Type (recur obj-expr)
           [(objT class-name)
            (find-field-in-tree field-name
                                class-name
                                t-classes)]
           [(intersectT t1 t2) ....] ; TODO
           [else (type-error obj-expr "object")])]
        [(sendI obj-expr method-name arg-expr)
         (local [(define obj-type (recur obj-expr))
                 (define arg-type (recur arg-expr))]
           (type-case Type obj-type
             [(objT class-name)
              (typecheck-send class-name method-name
                              arg-expr arg-type
                              t-classes interfs)]
             [(intT int-name)
              (typecheck-send-i int-name method-name
                                arg-expr arg-type
                                t-classes interfs)]
             [(intersectT t1 t2) ....] ; TODO
             [else
              (type-error obj-expr "object")]))]
        [(superI method-name arg-expr)
         (local [(define arg-type (recur arg-expr))
                 (define this-class
                   (if (objT? this-type)
                       (findT t-classes (objT-class-name this-type))
                       (error 'typecheck "interfaces cannot call `super`")))]
           (typecheck-send (classT-super-name this-class)
                           method-name
                           arg-expr arg-type
                           t-classes
                           interfs))]
        [(letI ns es bdy) (recur-with
                           (foldr2 (lambda (n e nv)
                                     (ext-env
                                      (tbind n
                                             (recur e))
                                      nv))
                                   tenv
                                   ns
                                   es)
                           bdy)]
        [(if0I tst tb fb) ;; TODO improve typechecking on if0s
         (type-case Type (recur tst)
           [(numT) (hamstrung-least-upper-bound (recur tb)
                                                (recur fb)
                                                t-classes
                                                interfs)]
           [else (type-error tst "num")])]))))

(module+ test
  (test/exn
   (typecheck-expr
    (superI 'f (numI 0))
    (list (pair 'a (classT 'Object '(foo) empty
                           (list (pair 'f
                                       (pair 'arg
                                             (methodT (numT)
                                                      (numT)
                                                      (idI 'arg)))))))
          (pair 'b (classT 'a empty empty empty)))
    (intT 'foo)
    mt-env
    (list (pair 'foo
                (interf '() (list (pair 'f (sig (numT) (numT))))))))
   "cannot call `super`")
  
  (define returns-interface
    (pair 'returns
          (classT 'Object
                  '()
                  '()
                  (list (pair 'ret-int
                              (pair 'arg
                                    (methodT (numT) (intT 'foo)
                                             (newI 'implementation '()))))))))
  (define impls-interface
    (pair 'implementation
          (classT 'Object
                  '(foo)
                  '()
                  (list (pair 'f
                              (pair 'arg
                                    (methodT (intT 'foo) (numT)
                                             (numI -1))))))))
  (define foo-int (pair 'foo
                        (interf '()
                                (list (pair 'f (sig (intT 'foo) (numT)))))))
  (define cs2 (list returns-interface impls-interface))
  (define is (list foo-int))
  (define tenv empty)
  (test (typecheck-expr
         (sendI (sendI (newI 'returns '())
                       'ret-int
                       (numI 0))
                'f (newI 'implementation '()))
         cs2 (objT 'Object) tenv is)
        (numT)))


(define (typecheck-send [class-name : Symbol]
                        [method-name : Symbol]
                        [arg-expr : ExpI]
                        [arg-type : Type]
                        [t-classes : ClassList]
                        [interfs : InterfList])
  (type-case MethodT (snd (find-method-in-tree
                           method-name
                           class-name
                           t-classes))
    [(methodT arg-type-m result-type body)
     (if (is-subtype? arg-type arg-type-m t-classes interfs)
         result-type
         (type-error arg-expr (to-string arg-type-m)))]))

;; tODO it should be possible to abstract over typecheck-send and this method
;; ; it would be especially nice of `methodT's had a `sig` instead of two types
(define (typecheck-send-i [i-name : Symbol]
                          [method-name : Symbol]
                          [arg-expr : ExpI]
                          [arg-type : Type]
                          [t-classes : ClassList]
                          [interfs : InterfList]) : Type
  (type-case (Optionof Signature) (find-sig method-name i-name interfs)
    [(none)
     ;; TODO we can probably do better error-message wise then this frankenstein lol
     (type-error method-name "found")]
    [(some s) (if (is-subtype? arg-type (sig-arg-t s) t-classes interfs)
                  (sig-ret-t s)
                  (type-error arg-expr (to-string (sig-ret-t s))))]))

(module+ test
  (define a (pair 'a (interf '() (list (pair 'f (sig (numT) (numT)))))))
  (define b (pair 'b (interf '(a) '())))
  (define c (pair 'c (interf '() '())))
  (define d (pair 'd (interf '() (list (pair 'g (sig (objT 'Object) (numT)))))))
  (define dag (list a b c d))
  (define cs (list (pair 'klass (classT 'Object '() '() '()))))

  (test (typecheck-send-i 'a 'f (numI 0) (numT) cs dag)
        (numT))
  (test/exn (typecheck-send-i 'missing 'f (numI 0) (numT) cs dag)
            "not found")
  (test/exn (typecheck-send-i 'a 'f (newI 'Object '()) (objT 'Object) cs dag)
            "no type")
  (test/exn (typecheck-send-i 'c 'f (numI 0) (numT) cs dag)
            "not found")
  (test (typecheck-send-i 'd 'g (newI 'klass '()) (objT 'klass) cs dag)
        (numT))
  (test/exn (typecheck-send-i 'd 'g (numI 0) (numT) cs dag)
            "no type"))


(define (typecheck-method [method : MethodT]
                          [this-type : Type]
                          [t-classes : ClassList]
                          [tenv : T-Env]
                          [interfs : InterfList]) : ()
  (type-case MethodT method
    [(methodT arg-type result-type body-expr)
     (let* ([fields (get-all-fields (objT-class-name this-type) t-classes)]
            [new-env (foldl (lambda (f env)
                              (ext-env (tbind (fst f) (snd f))
                                       env))
                            tenv
                            fields)])
       (if (is-subtype? (typecheck-expr body-expr t-classes
                                        this-type new-env interfs)
                        result-type
                        t-classes
                        interfs)
           (values)
           (type-error body-expr (to-string result-type))))]))

(define (check-override [method-name : Symbol]
                        [method : MethodT]
                        [this-class : ClassT]
                        [t-classes : ClassList]
                        [interfs : InterfList])
  (local [(define super-name
            (classT-super-name this-class))
          (define super-method
            (try
             ;; Look for method in superclass:
             (snd (find-method-in-tree method-name
                                       super-name
                                       t-classes))
             ;; no such method in superclass:
             (lambda () method)))]
    (if (and (equal? (methodT-arg-type method)
                     (methodT-arg-type super-method))
             ;; NOTE: changed overrides to be covariant in result type
             ; but left arg type as it was i.e. invariant
             (is-subtype? (methodT-result-type method)
                          (methodT-result-type super-method)
                          t-classes
                          interfs))
        (values)
        (error 'typecheck (string-append
                           "bad override of "
                           (to-string method-name))))))

(module+ test
  (define class-list
    (list
     (pair 'Foo
           (classT 'Object '() '()
                   (list (pair 'f
                               (pair 'arg
                                     (methodT (numT) (objT 'Foo) (thisI)))))))
     (pair 'FooSubclass
           (classT 'Foo '() '()
                   (list (pair 'f
                               (pair 'arg
                                     (methodT (numT) (objT 'FooSubclass) (thisI)))))))))
  (test (check-override 'f (methodT (numT) (objT 'FooSubclass) (thisI))
                        (snd (second class-list))
                        class-list empty)
        (values))
  (test/exn (check-override 'f (methodT (numT) (objT 'Object) (thisI))
                            (snd (second class-list))
                            class-list empty)
            "bad override")
  (test/exn (check-override 'f (methodT (objT 'Foo) (objT 'Foo) (thisI))
                            (snd (second class-list))
                            class-list empty)
            "bad override"))

;;---------typecheck a class-----------

(define (typecheck-class [class-name : Symbol]
                         [t-class : ClassT]
                         [t-classes : ClassList]
                         [interfs : InterfList]
                         [tenv : T-Env])
  (type-case ClassT t-class
    [(objectClass) (list (values))]
    [(classT super-name impls fields methods)
     (if (all? impls
               (lambda (impl)
                 (valid-impl? class-name impl
                              t-classes interfs)))
         (map (lambda (m)
                (let ([m-name (fst m)]
                      [arg-name (fst (snd m))]
                      [m-sig (snd (snd m))])
                  (begin
                    (typecheck-method m-sig
                                      (objT class-name)
                                      t-classes
                                      (ext-env
                                       (tbind arg-name (methodT-arg-type m-sig))
                                       tenv)
                                      interfs)
                    (check-override (fst m) (snd (snd m)) t-class t-classes interfs))))
              methods)
         (error 'typecheck-class (string-append "invalid implementation: "
                                                (symbol->string class-name))))]))

(define (typecheck [a : ExpI]
                   [t-classes : ClassList]
                   [interfs : InterfList]
                   [tenv : T-Env]) : Type
  (begin
    (map (lambda (tc)
           (typecheck-class (fst tc) (snd tc) t-classes interfs tenv))
         t-classes)
    (typecheck-expr a t-classes (objT 'Object) tenv interfs)))

;; ----------------------------------------

(module+ test
  (test (typecheck-class 'foo OBJECT '() '() empty)
        (list (values)))
  
  (define posn-t-class
    (values 'Posn
            (classT 'Object
                    empty
                    (list (values 'x (numT)) (values 'y (numT)))
                    (list (values 'mdist
                                  (values '_
                                          (methodT (numT) (numT) 
                                                   (plusI (getI (thisI) 'x) (getI (thisI) 'y)))))
                          (values 'addDist
                                  (values 'arg
                                          (methodT (objT 'Posn) (numT)
                                                   (plusI (sendI (thisI) 'mdist (numI 0))
                                                          (sendI (idI 'arg) 'mdist (numI 0))))))))))
  
  (define posn3D-t-class 
    (values 'Posn3D
            (classT 'Posn
                    empty
                    (list (values 'z (numT)))
                    (list (values 'mdist
                                  (values 'arg
                                          (methodT (numT) (numT)
                                                   (plusI (getI (thisI) 'z) 
                                                          (superI 'mdist (idI 'arg))))))))))

  (define square-t-class 
    (values 'Square
            (classT 'Object
                    empty
                    (list (values 'topleft (objT 'Posn)))
                    (list))))
  
  (define (typecheck-posn a)
    (typecheck a
               (list posn-t-class posn3D-t-class square-t-class)
               (list) (list)))

  (define new-posn27 (newI 'Posn (list (numI 2) (numI 7))))
  (define new-posn531 (newI 'Posn3D (list (numI 5) (numI 3) (numI 1))))
  (define new-posn079 (newI 'Posn3D (list (numI 0) (numI 7) (numI 9))))

  
  ;;if0
  (test (typecheck-posn (if0I (numI 0) (numI 1) (plusI (numI 0) (numI -1))))
        (numT))

  (test (typecheck-posn (if0I (numI 1)
                              new-posn531
                              (newI 'Square (list (newI 'Posn (list (numI 0) (numI 1)))))))
        (objT 'Object))
  (test (typecheck-posn (if0I (numI 2903)
                              (newI 'Object '())
                              new-posn079))
        (objT 'Object))
  (test/exn (typecheck-posn (if0I new-posn079
                                  (numI 1)
                                  (numI 2)))
            "no type")
  
  (test/exn (typecheck-posn (if0I new-posn079
                                  (numI 0)
                                  (numI 1)))
            "no type")
  (test/exn (typecheck-posn (if0I (numI 3920)
                                  (numI 0)
                                  (newI 'Square '())))
            "no type")
  (test (typecheck-posn (if0I (numI 0)
                              new-posn079
                              new-posn27))
        (objT 'Posn))

  (test (typecheck (if0I (numI 0)
                         (newI 'Object '())
                         (sendI (newI 'a '()) 'f (numI 0)))
                   (list (pair 'a
                               (classT
                                'Object
                                '(foo)
                                '()
                                (list (pair
                                       'f (pair 'arg
                                                (methodT (numT)
                                                         (intT 'foo)
                                                         (thisI))))))))
                   (list (pair 'foo
                               (interf '()
                                       (list (pair 'f
                                                   (sig (numT) (intT 'foo)))))))
                   empty)
        (objT 'Object))
  (test (typecheck (if0I (numI 0)
                         (newI 'c '())
                         (sendI (newI 'a '()) 'f (numI 0)))
                   (list (pair 'a
                               (classT
                                'Object
                                '(foo)
                                '()
                                (list (pair
                                       'f (pair 'arg
                                                (methodT (numT)
                                                         (intT 'foo)
                                                         (thisI)))))))
                         (pair 'b
                               (classT
                                'Object
                                '(foo) '()
                                (list (pair
                                       'f (pair 'arg
                                                (methodT (numT)
                                                         (intT 'foo)
                                                         (thisI)))))))
                         (pair 'c
                               (classT
                                'b
                                '() '() '())))
                   (list (pair 'foo
                               (interf '()
                                       (list (pair 'f
                                                   (sig (numT) (intT 'foo)))))))
                   empty)
        (intT 'foo))
  
  ;; interface typechecking
  (define FooBadImpl (pair 'Foo
                           (classT 'Object
                                   '(IBool)
                                   '()
                                   '())))
  ; E : INum => E has [->num : num -> num]
  (define INum (pair 'INum (interf '()
                                   (list (pair '->num
                                               (sig (numT) (numT)))))))
  ; E : IBool => E has [& : IBool -> IBool]
  ;                    [|| : IBool -> IBool]
  (define IBool (pair 'IBool (interf '(INum)
                                     (list (pair '&
                                                 (sig (intT 'IBool)
                                                      (intT 'IBool)))
                                           (pair '||
                                                 (sig (intT 'IBool)
                                                      (intT 'IBool)))))))
  ; E : IFoo => E
  (define IFoo (pair 'IFoo (interf '() '())))
  (define IBar (pair 'IBar (interf '(IBool) '())))
  (define IBuz (pair 'IBuz (interf '(IBar) '())))
  
  (define intf-env (list INum
                         IBool
                         IFoo
                         IBar
                         IBuz))
  (define SomeClass (pair 'SomeClass
                          (classT 'Object
                                  '(IFoo)
                                  '()
                                  '())))
  (define 2DNumber (pair '2DNumber
                         (classT 'Object
                                 '(INum)
                                 (list (pair 'x (numT))
                                       (pair 'y (numT)))
                                 (list (pair '->num
                                             (pair 'arg
                                                   (methodT (numT) (numT) (multI (getI (thisI) 'x)
                                                                                 (getI (thisI) 'y)))))))))
  (define 3DNumber (pair '3DNumber
                         (classT '2DNumber
                                 '()
                                 (list (pair 'z (numT)))
                                 (list (pair '->num
                                             (pair 'arg
                                                   (methodT (numT) (numT) (multI (getI (thisI) 'z)
                                                                                 (superI '->num (numI -1))))))))))
  (define True (pair 'True
                     (classT 'Object
                             '(IBool)
                             '()
                             (list (pair '->num
                                         (pair 'arg
                                               (methodT (numT) (numT) (numI 0))))
                                   (pair '&
                                         (pair 'arg (methodT (intT 'IBool)
                                                             (intT 'IBool)
                                                             (thisI))))
                                   (pair '||
                                         (pair 'arg (methodT (intT 'IBool)
                                                             (intT 'IBool)
                                                             (thisI))))))))
  (define interfs intf-env)
  (define klasses (list SomeClass 2DNumber 3DNumber True))
  (test/exn (typecheck-class 'Foo
                             (snd FooBadImpl)
                             (append klasses (list FooBadImpl))
                             interfs
                             empty)
            "invalid implementation")
  (test (typecheck-class 'True
                         (snd True)
                         klasses interfs empty)
        (list (values) (values) (values)))
  
  ;; identifiers and let -- no interfaces involved
  (test/exn (typecheck-expr (idI 'x) '() (numT) '() '())
            "not found")
  (test (typecheck-expr (idI 'foo)
                        '()
                        (numT)
                        (list (tbind 'foo (numT)))
                        '())
        (numT))
  (test (typecheck-expr (letI '(x y)
                              (list (numI 0)
                                    (numI 2))
                              (plusI (idI 'x)
                                     (idI 'y)))
                        '()
                        (numT)
                        '()
                        '())
        (numT))
  (test/exn (typecheck-expr (letI '(x)
                                  (list (newI 'Object '()))
                                  (plusI (numI 1)
                                         (idI 'x)))
                            '()
                            (numT)
                            '()
                            '())
            "no type")
  (test (typecheck-posn (sendI new-posn27 'mdist (numI 0)))
        (numT))
  (test (typecheck-posn (sendI new-posn531 'mdist (numI 0)))
        (numT))
  (test (typecheck-posn (sendI new-posn531 'addDist new-posn27))
        (numT))
  (test (typecheck-posn (sendI new-posn27 'addDist new-posn531))
        (numT))

  (test (typecheck-posn (newI 'Square (list (newI 'Posn (list (numI 0) (numI 1))))))
        (objT 'Square))
  (test (typecheck-posn (newI 'Square (list (newI 'Posn3D (list (numI 0) (numI 1) (numI 3))))))
        (objT 'Square))

  (test (typecheck (multI (numI 1) (numI 2))
                   empty empty empty)
        (numT))

  (test/exn (typecheck-posn (sendI (numI 10) 'mdist (numI 0)))
            "no type")
  (test/exn (typecheck-posn (sendI new-posn27 'mdist new-posn27))
            "no type")
  (test/exn (typecheck (plusI (numI 1) (newI 'Object empty))
                       empty empty empty)
            "no type")
  (test/exn (typecheck (plusI (newI 'Object empty) (numI 1))
                       empty empty empty)
            "no type")
  (test/exn (typecheck (plusI (numI 1) (newI 'Object (list (numI 1))))
                       empty empty empty)
            "no type")
  (test/exn (typecheck (getI (numI 1) 'x)
                       empty empty empty)
            "no type")
  (test/exn (typecheck (numI 10)
                       (list posn-t-class
                             (values 'Other
                                     (classT 'Posn
                                             (list)
                                             (list)
                                             (list (values 'mdist
                                                           (values '_
                                                                   (methodT (objT 'Object) (numT)
                                                                            (numI 10))))))))
                       empty empty)
            "bad override")
  (test/exn (typecheck-method (methodT (numT) (objT 'Object) (numI 0)) (objT 'Object) empty '() '())
            "no type")
  (test/exn (typecheck (numI 0)
                       (list square-t-class
                             (values 'Cube
                                     (classT 'Square
                                             empty
                                             empty
                                             (list
                                              (values 'm
                                                      (values 'arg
                                                              (methodT (numT) (numT)
                                                                       ;; No such method in superclass:
                                                                       (superI 'm (numI 0)))))))))
                       empty empty)
            "not found"))

;; ----------------------------------------

(define strip-types : (ClassT -> ClassI)
  (lambda (t-class)
    (type-case ClassT t-class
      [(objectClass) (objI)]
      [(classT super-name impls fields methods)
       (classI
        super-name
        (map fst fields)
        (map (lambda (m)
               (values (fst m)
                       (type-case MethodT (snd (snd m))
                         [(methodT arg-type result-type body-expr)
                          (values (fst (snd m)) body-expr)])))
             methods))])))

(module+ test
  (test (strip-types (classT 'Object
                             '(Foo Bar Baz)
                             (list (pair 'x (numT))
                                   (pair 'self (objT 'Foo)))
                             (list (pair 'ident
                                         (pair 'arg
                                               (methodT (objT 'Object)
                                                        (objT 'Object)
                                                        (idI 'arg)))))))
        (classI 'Object
                '(x self)
                (list (values 'ident (values 'arg (idI 'arg))))))
  (test (strip-types OBJECT)
        (objI)))

(define interp-t : (ExpI ClassList -> Value)
  (lambda (a t-classes)
    (interp-i a
              (map (lambda (c)
                     (values (fst c) (strip-types (snd c))))
                   t-classes))))

(module+ test  
  (define (interp-t-posn a)
    (interp-t a
              (list posn-t-class posn3D-t-class)))

  (test (interp-t-posn (sendI new-posn27 'mdist (numI 0)))
        (numV 9))
  (test (interp-t-posn (sendI new-posn531 'mdist (numI 0)))
        (numV 9))
  (test (interp-t-posn (sendI new-posn531 'addDist new-posn27))
        (numV 18))
  (test (interp-t-posn (sendI new-posn27 'addDist new-posn531))
        (numV 18)))
