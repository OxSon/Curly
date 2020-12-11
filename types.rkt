#lang plait

(require "class.rkt"
         "inherit.rkt"
         "utils.rkt")

(module+ test
  (print-only-errors #t))

;;-------------------------------
;; Plait-level type definitions
;; for Curly constructs:
;; Type, Method, Typed Class
;;-------------------------------

(define-type Type
  (numT)
  (objT [class-name : Symbol])
  (intT [name : Symbol])
  (intersectT [t1 : Type] [t2 : Type]))
 
(define-type MethodT
  (methodT [arg-type : Type]
           [result-type : Type]
           [body : ExpI]))

(define-type-alias Method (Symbol * (Symbol * MethodT)))
(define-type-alias Field (Symbol * Type))

(define-type ClassT
  (objectClass)
  (classT [super-name : Symbol]
          [impls : (Listof Symbol)]
          [fields : (Listof Field)]
          [methods : (Listof Method)]))

(define OBJECT (objectClass))

(define-type-alias ClassList (Listof (Symbol * ClassT)))

;;-----------------------------------

(define (findT [t-classes : ClassList] [name : Symbol])
  (if (symbol=? name 'Object)
      OBJECT
      (find t-classes name)))

(module+ test
  (test (findT '() 'Object)
        OBJECT)
  (test (findT (list (pair 'Foo
                           (classT 'Foo '() '() '())))
               'Foo)
        (classT 'Foo empty empty empty)))

(define (is-subclass? name1 name2 t-classes)
  (cond
    [(symbol=? name1 name2) #t]
    [(symbol=? name1 'Object) #f]
    [else (is-subclass? (classT-super-name (find t-classes name1))
                        name2 t-classes)]))

(module+ test
  (define a-t-class (values 'A (classT 'Object empty empty empty)))
  (define b-t-class (values 'B (classT 'A empty empty empty)))

  (test (is-subclass? 'Object 'Object empty)
        #t)
  (test (is-subclass? 'A 'B (list a-t-class b-t-class))
        #f)
  (test (is-subclass? 'B 'A (list a-t-class b-t-class))
        #t))

;;--------------------------

(define (type-error a msg)
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string a)
                      (string-append " not "
                                     msg)))))

(module+ test
  (test/exn (type-error (numI 2) "num")
            "no type: (numI 2) not num"))

;;--Plait-level type definitions for interfaces and their components----

(define-type Signature
  (sig [arg-t : Type]
       [ret-t : Type]))

;; ASSUMPTIONS: interfaces do not attempt to override methods of their superinterfaces
;; TODO they should be able to override, subject to the same rules as class overrides.
(define-type Interface
  (interf [exts : (Listof Symbol)]
          [requires : (Listof (Symbol * Signature))]))

(define-type-alias InterfList (Listof (Symbol * Interface)))

;; ASSUMPTIONS:
;; 1) both `name1` and `name2` are valid interfaces included in `interfs`
;; 2) the interfs in `interfs` form a DAG (no cycles)
(define is-subinterface? : (Symbol Symbol (Listof (Symbol * Interface)) -> Boolean)
  (lambda (name1 name2 interfs)
    (cond
      [(symbol=? name1 name2) #t]
      [else (type-case Interface (find interfs name1)
              [(interf exts reqs)
               (any? exts (lambda (x)
                            (is-subinterface? x name2 interfs)))])])))

(module+ test
  (define I0 (pair 'I0
                   (interf '() '())))
  (define Iλ (pair 'Iλ
                   (interf '() '())))
  (define I1 (pair 'I1
                   (interf '(Iλ I0) '())))
  (define I2 (pair 'I2
                   (interf '(I0 I1) '())))
  (define I3 (pair 'I3
                   (interf '(I2) '())))
  (define I4 (pair 'I4
                   (interf '(I3 Iλ) '())))
#| DAG of the above:

    Iλ <------ I4 -----------
    ^                       |
    |  --> I0 <--      I3 <-|
    |  |        |      |
    ---I1 <-----I2 <---|
|#
  (define ilist (list I0 Iλ I1 I2 I3 I4))

  (test (is-subinterface? 'I0 'I1 ilist)
        #f)
  (test (is-subinterface? 'I1 'Iλ ilist)
        #t)
  (test (is-subinterface? 'I2 'I1 ilist)
        #t)
  (test (is-subinterface? 'I3 'I0 ilist)
        #t)
  (test (is-subinterface? 'I4 'I0 ilist)
        #t))

;; ----------------------------------------

(find-sig : (Symbol Symbol InterfList -> (Optionof Signature)))
(define (find-sig method entry-point dag)
  (type-case Interface (find dag entry-point)
    [(interf exts reqs)
     (cond
       [(member method (map fst reqs))
        (some (find reqs method))]
       [(empty? exts) (none)]
       [else (foldl (lambda (next-i acc)
                     (type-case (Optionof Signature) acc
                       [(none) (find-sig method next-i dag)]
                       [else acc]))
                   (none)
                   exts)])]))

(module+ test
  (define target (some (sig (numT) (numT))))
  (define a (pair 'a (interf '() (list (pair 'f (some-v target))))))
  (define b (pair 'b (interf '(a c d) '())))
  (define c (pair 'c (interf '() '())))
  (define d (pair 'd (interf '(a c) '())))
  (define e (pair 'e (interf '(c) '())))
  (define f (pair 'f (interf '(d) '())))
  (define g (pair 'g (interf '(c d) '())))
  (define dag (list a b c d e f g))

  (test (find-sig 'f 'a dag)
        target)
  (test (find-sig 'f 'b dag)
        target)
  (test (find-sig 'f 'c dag)
        (none))
  (test (find-sig 'f 'd dag)
        target)
  (test (find-sig 'f 'e dag)
        (none))
  (test (find-sig 'f 'f dag)
        target)
  (test (find-sig 'f 'g dag)
        target))
 

;; ----------------------------------------

(define (is-subtype? t1 t2 t-classes interfs)
  (type-case Type t1
    [(objT name1)
     (type-case Type t2 
       [(objT name2)
        (is-subclass? name1 name2 t-classes)]
       [(intT name2)
        (implements? name1 name2
                     t-classes interfs)]
       [(intersectT t3 t4) ....]
       [else #f])]
    [(intT name1)
     (type-case Type t2
       [(intT name2) (is-subinterface? name1 name2 interfs)]
       [(intersectT t3 t4) ....]
       [else #f])]
    [(intersectT t3 t4) ....]
    [else (equal? t1 t2)]))

(module+ test
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
  (define klasses (list SomeClass 2DNumber 3DNumber True))

  (test (is-subtype? (intersectT (objT 'True) (intT 'INum)) (objT 'True) klasses intf-env)
        #t)
  (test (is-subtype? (intersectT (objT 'True) (intT 'INum)) (intT 'INum) klasses intf-env)
        #t)
  (test (is-subtype? (objT 'True) (intersectT (objT 'True) (intT 'INum)) klasses intf-env)
        #f)
  (test (is-subtype? (intT 'INum) (numT) klasses intf-env)
        #f)
  (test (is-subtype? (intT 'Missing) (objT 'whatever) klasses intf-env)
        #f)
  (test (is-subtype? (objT 'True) (intT 'INum) klasses intf-env)
        #t)
  (test (is-subtype? (objT '2DNumber) (intT 'INum) klasses intf-env)
        #t)
  (test (is-subtype? (objT '2DNumber) (intT 'IBool) klasses intf-env)
        #f)
  (test (is-subtype? (intT 'IFoo) (objT 'boogabooga) klasses intf-env)
        #f)
  (test (is-subtype? (intT 'IBool) (intT 'INum) klasses intf-env)
        #t)
  (test (is-subtype? (intT 'IFoo) (intT 'INum) klasses intf-env)
        #f)
  (test (is-subtype? (intT 'INum) (intT 'IBool) klasses intf-env)
        #f)
  (test (is-subtype? (intT 'IBar) (intT 'INum) klasses intf-env)
        #t)
  (test (is-subtype? (intT 'IBuz) (intT 'INum) klasses intf-env)
        #t)
  (test (is-subtype? (numT) (numT) empty empty)
        #t)
  (test (is-subtype? (numT) (objT 'Object) empty empty)
        #f)
  (test (is-subtype? (objT 'Object) (numT) empty empty)
        #f)
  (test (is-subtype? (objT 'A) (objT 'B) (list a-t-class b-t-class) empty)
        #f)
  (test (is-subtype? (objT 'B) (objT 'A) (list a-t-class b-t-class) empty)
        #t))

;; ----------------------------------------

(define-type-alias T-Env (Listof (Symbol * Type)))
(define (tbind [n : Symbol] [t : Type])
  (values n t))

(module+ test
  (test (tbind 'foo (objT 'bar))
        (values 'foo (objT 'bar)))
  (test (find (list (tbind 'foo (numT))
                    (tbind 'bar (objT 'baz)))
              'bar)
        (objT 'baz)))

;; ----------------------------------------
;TODO BLEHHH!!!

(define (least-upper-bound t1 t2 t-classes interfs tenv)
  ....)

(define (supers-of [c-name : Symbol] [t-classes : ClassList]) : (Listof Symbol)
  (type-case ClassT (findT t-classes c-name)
    [(objectClass) '(Object)]
    [(classT super-name i f m)
     (cons c-name (supers-of super-name t-classes))]))

;; I got majorly stuck on finding an accurate least upper bound
;; when interfaces are in play and ran out of time.
;; For now, we will just implement a cheap imitation of java's behavior,
;; but without intersection types, and only considering
;; a handful of basic, common use-cases
;; for least-upper-bounds involving interface types.
;; Assumes the classes named are valid and present in t-classes.
(define (hamstrung-least-upper-bound t1 t2 t-classes interfs) : Type
  (type-case Type t1
    [(numT) (if (numT? t2)
                (numT)
                (type-error t2 "num"))]
    [(objT name1)
     (type-case Type t2
       [(objT name2)
        (let ([nearest-class (some-v (nearest-common-superclass t1 t2 t-classes))])
          (if (symbol=? (objT-class-name nearest-class)
                        'Object)
              (try (some-v (shared-implementation t1 t2 t-classes))
                   (lambda () nearest-class))
              nearest-class))]
       [(intT name2) (if (implements? name1 name2 t-classes interfs)
                         t2
                         ; we can always fall back to Object since we know the underlying value
                         ; for an interface type will be an object at runtime
                         (objT 'Object))]
       [else (type-error t2 "object")])]
    [(intT name1)
     (type-case Type t2
       [(objT name2) (hamstrung-least-upper-bound t2 t1 t-classes interfs)]
       [(intT name2) (if (is-subtype? t1 t2 t-classes interfs)
                         t2
                         (if (is-subtype? t2 t1 t-classes interfs)
                             t1
                             (error 'hamstrung-lub "no type")))]
       [else (error 'hamstrung-lub "no type")])]
    [else (error 'hamstrung-lub "no type")]))

(define (shared-implementation c1 c2 t-classes) : (Optionof Type)
  (type-case Type c1
    [(objT name1)
     (type-case Type c2
       [(objT name2)
        (let ([result (has-type (intersect-point
                                 (get-all-direct-impls name1 t-classes)
                                 (get-all-direct-impls name2 t-classes))
                                : (Optionof Symbol))])
          (if (some? result)
              (some (intT (some-v result)))
              (none)))]
       [else (error 'shared-impl
                    (string-append (to-string c2) " is not an object type"))])]
    [else (error 'shared-impl
                 (string-append (to-string c1) " is not an object type"))]))

(define (get-all-direct-impls c-name t-classes)
  (type-case ClassT (findT t-classes c-name)
    [(objectClass) empty]
    [(classT super-name impls _ __)
     (append impls (get-all-direct-impls super-name t-classes))]))

(module+ test
  (define ham hamstrung-least-upper-bound)
  (test (ham (numT) (numT) '() empty)
        (numT))
  (test/exn (ham (numT) (objT 'foo) '() empty)
            "no type")
  (test/exn (ham (numT) (intT 'bar) '() empty)
            "no type")
  (test (ham (objT 'a) (objT 'Object)
             (list (pair 'a (classT 'Object '() '() '())))
             empty)
        (objT 'Object))
  (test (ham (objT 'b) (objT 'c)
             (list (pair 'a (classT 'Object empty empty empty))
                   (pair 'b (classT 'a empty empty empty))
                   (pair 'c (classT 'a empty empty empty)))
             empty)
        (objT 'a))
  (test (ham (intT 'foo) (intT 'foo) '() (list (pair 'foo (interf empty empty))))
            (intT 'foo))
  (test (ham (intT 'foo) (intT 'bar) '() (list (pair 'foo (interf '(bar) empty))
                                               (pair 'bar (interf '() empty))))
        (intT 'bar))
  (test (ham (intT 'foo) (intT 'bar) '() (list (pair 'foo (interf '() empty))
                                               (pair 'bar (interf '(foo) empty))))
        (intT 'foo))
  (test (ham (objT 'foo) (intT 'bar)
             (list (pair 'foo
                                                 (classT 'Object
                                                         '(bar) empty empty)))
             (list (pair 'bar (interf empty empty))))
        (intT 'bar))
  (test (ham (objT 'sub) (intT 'foo)
             (list (pair 'super (classT 'Object '(bar) empty empty))
                   (pair 'sub (classT 'super '() empty empty)))
             (list (pair 'foo (interf empty empty))
                   (pair 'bar (interf '(foo) empty))))
        (intT 'foo))
  (test (ham (intT 'foo) (objT 'sub)
             (list (pair 'super (classT 'Object '(bar) empty empty))
                   (pair 'sub (classT 'super '() empty empty)))
             (list (pair 'foo (interf empty empty))
                   (pair 'bar (interf '(foo) empty))))
        (intT 'foo)))

(nearest-common-superclass : (Type Type ClassList -> (Optionof Type)))
(define (nearest-common-superclass t1 t2 t-classes)
  (type-case Type t1
    [(objT name1)
     (type-case Type t2
       [(objT name2)
        ;; TODO this could be done more efficiently 
        (some (objT (some-v (intersect-point (supers-of name1 t-classes)
                                             (supers-of name2 t-classes)))))]
       [(intersectT t3 t4) ....]
       [else (none)])]
    [(intersectT t3 t4) ....]
    [else (none)]))

;; Got majorly stuck on this one :(
(nearest-common-interface : (Type Type ClassList InterfList -> (Optionof Type)))
(define (nearest-common-interface t1 t2 t-classes interfs)
  (type-case Type t1
    [(objT name1)
     (type-case Type t2
       [(objT name2) ....]
       [(intT name2) ....]
       [(intersectT t3 t4) ....]
       [else (none)])]
    [(intT name1)
     (type-case Type t2
       [(objT name2) ....]
       [(intT name2) ....]
       [(intersectT t3 t4) ....]
       [else (none)])]
    [(intersectT t3 t4) ....]
    [else (none)]))

;; the following definitions should really be in the test submodule,
;; but there seems to be a bug with macros defined in submodules?
;; The typechecker kept complaining about `def-mt` being undefined
;; even though it was there. When I moved JUST the macro to top-level,
;; then it didn't complain about `def-mt`, but it did randomly complain about
;; (def-mt h b) with "undefined h" message which shouldn't happen if I
;; understand the process here correctly. Perhaps the typechecker
;; is not allowing expansion to complete fully before typechecking causing
;; the issues described above?
(define (mt-class super-name) (classT super-name '() '() '()))
(define-syntax-rule (def-mt name super-name)
  (define name (pair 'name (mt-class 'super-name))))

(def-mt aa Object) (def-mt bb Object) (def-mt cc Object) (def-mt dd Object)
(def-mt ee aa) (def-mt ff aa) (def-mt gg bb) (def-mt hh bb)
(def-mt ii hh) (def-mt jj hh)
(def-mt kk jj)
(def-mt ll kk) (def-mt mm kk)


(module+ test
  (define clist (list aa bb cc dd ee ff gg hh ii jj kk ll mm))

  (test (supers-of 'aa clist)
        '(aa Object))
  (test (supers-of 'ff clist)
        '(ff aa Object))
  (test (supers-of 'll clist)
        '(ll kk jj hh bb Object))

  (test (nearest-common-superclass (objT 'kk) (objT 'll) clist)
        (some (objT 'kk)))
  (test (nearest-common-superclass (objT 'kk) (objT 'ii) clist)
        (some (objT 'hh)))
  (test (nearest-common-superclass (objT 'kk) (objT 'gg) clist)
        (some (objT 'bb)))
  (test (nearest-common-superclass (objT 'ee) (objT 'ff) clist)
        (some (objT 'aa)))
  (test (nearest-common-superclass (objT 'ee) (objT 'mm) clist)
        (some (objT 'Object)))
  (test (nearest-common-superclass (objT 'Object) (objT 'ff) clist)
        (some (objT 'Object)))
  (test (nearest-common-superclass (objT 'ee) (objT 'Object) clist)
        (some (objT 'Object)))
  ;; non object types will never have a common superclass
  (test (nearest-common-superclass (intT 'foo) (objT 'Object) clist)
        (none))
  (test (nearest-common-superclass (objT 'foo) (intT 'bar) clist)
        (none))
  (test (nearest-common-superclass (numT) (objT 'foo) clist)
        (none))
  (test (nearest-common-superclass (objT 'foo) (numT) clist)
        (none))
  (test (nearest-common-superclass (numT) (numT) clist)
        (none))
  
  (test (least-upper-bound (numT) (numT) '() '() '())
        (numT)))

;; ----------------------------------------

(define (get-all-field-types class-name t-classes)
      (type-case ClassT (findT t-classes class-name)
        [(objectClass) empty]
        [(classT super-name impls fields methods)
         (append
          (get-all-field-types super-name t-classes)
          (map snd fields))]))

(define (get-all-fields class-name t-classes)
  (type-case ClassT (findT t-classes class-name)
    [(objectClass) empty]
    [(classT super-name impls fields methods)
     (append (get-all-fields super-name t-classes)
             fields)]))

(module+ test
  (define FooClass (classT 'Object
                           empty
                           (list (values 'x (numT))
                                 (values 'self (objT 'Foo)))
                           (list (values 'ident (values 'arg (methodT (numT)
                                                                      (numT)
                                                                      (idI 'arg)))))))
  (test (get-all-field-types 'Foo (list (values 'Foo FooClass)))
        (list (numT) (objT 'Foo)))
  (test (get-all-field-types 'Object '())
        '())
  (test (get-all-fields 'Foo (list (values 'Foo FooClass)))
        (list (pair 'x (numT)) (pair 'self (objT 'Foo)))))

;; ----------------------------------------

(define (make-find-in-tree class-items)
  (lambda (name class-name t-classes)
    (if (symbol=? class-name 'Object)
        (error 'find "Object class has no components")
        (local [(define t-class (find t-classes class-name))
            (define items (class-items t-class))
            (define super-name 
              (classT-super-name t-class))]
      (if (equal? super-name 'Object)
          (find items name)
          (try (find items name)
               (lambda ()
                 ((make-find-in-tree class-items)
                  name
                  super-name
                  t-classes))))))))

(define find-field-in-tree
  (make-find-in-tree classT-fields))

(define find-method-in-tree
  (make-find-in-tree classT-methods))


(module+ test
  (test (find-field-in-tree 'x 'foo (list (pair 'foo
                                                (classT 'bar
                                                        '()
                                                        '()
                                                        '()))
                                          (pair 'bar
                                                (classT 'Object
                                                        '()
                                                        (list (pair 'x (numT)))
                                                        '()))))
        (numT)))

(module+ test
  (test/exn (find-field-in-tree 'x 'Object '())
            "no components"))

(define (implements? class-name interf-name t-classes interfs)
  (type-case ClassT (findT t-classes class-name)
    [(objectClass) #f] ; base case
    [(classT super-name impls fields methods)
     (cond
       [(any? impls
              (lambda (impl)
                (is-subtype? (intT impl) (intT interf-name)
                             t-classes interfs)))
        #t]
       [else (implements? super-name interf-name
                          t-classes interfs)])]))

;; A method fulfills a signature when:
;; 1) arg type is invariant 
;; 2) ret type is covariant
;; The above matches our rules for method overrides
(define (fulfills? [m : MethodT]
                   [sig : Signature]
                   [klasses : ClassList]
                   [interfs : InterfList])
  (and (equal? (methodT-arg-type m) (sig-arg-t sig))
       (is-subtype? (methodT-result-type m)
                    (sig-ret-t sig)
                    klasses
                    interfs)))

;; assumes the class, or one of its supers, does implement a method
;; with the given name, but does not assume that the named method
;; necessarily meets the signature requirement
(define (fulfilled?  [class-name : Symbol]
                     [req : (Symbol * Signature)]
                     [t-classes : ClassList]
                     [interfs : InterfList])
  : Boolean
  (let/cc k
    (fulfills? (snd (try (find-method-in-tree (fst req)
                                              class-name
                                              t-classes)
                         (lambda () (k #f))))
               (snd req)
               t-classes
               interfs)))

;; ASSUMPTIONS:
;; 1) no two interfaces in `interfs` name the same method
;; 2) class and interf named are valid and present in t-classes/interfs
(define (valid-impl? [class-name : Symbol]
                     [i-name : Symbol]
                     [t-classes : ClassList]
                     [interfs : InterfList]) : Boolean
  (type-case Interface (find interfs i-name)
    [(interf exts reqs)
     (and (all? reqs
                (lambda (req)
                  (fulfilled? class-name req t-classes interfs)))
          (all? exts
                (lambda (ext)
                  (valid-impl? class-name ext t-classes interfs))))]))

(module+ test
    ;; Recall:
  ;;klasses = (list
  ;; SomeClass #|implements IFoo|#
  ;; 2DNumber  #|implements INum|#
  ;; 3DNumber
  ;; True  #|implements IBool|#
  ;; )
  (define interfs intf-env)
  ;; interfs = (list
  ;; INum => [->num : num -> num]
  ;; IBool => INum + [& : IBool -> IBool]
  ;; IFoo => []
  ;; IBar => IBool + []
  ;; IBuz => IBar + []
  ;; )
  ;;
  (define (req name arg-t res-t) (pair name (sig arg-t res-t)))
  (test (fulfilled? '2DNumber
                    (req '->num (numT) (numT))
                    klasses interfs)
        #t)
  (test (fulfilled? '3DNumber
                    (req '->num (numT) (numT))
                    klasses interfs)
        #t)
  (test (fulfilled? 'SomeClass
                    (req '->num (numT) (numT))
                    klasses interfs)
        #f)
  (test (fulfilled? 'True
                    (req '->num (numT) (numT))
                    klasses interfs)
        #t)
  (test (fulfilled? 'True
                    (req '& (intT 'IBool) (intT 'IBool))
                    klasses interfs)
        #t)
  ;; arg types are invariant
  (test (fulfilled? 'True
                    (req '& (intT 'INum) (intT 'IBool))
                    klasses interfs)
        #f)
  (test (fulfilled? 'True
                    (req '& (intT 'IBar) (intT 'IBool))
                    klasses interfs)
        #f)
  ;;ret types are covariant
  (test (fulfilled? 'True
                    (req '& (intT 'IBool) (intT 'INum))
                    klasses interfs)
        #t)

  
  (define (meth t1 t2) (methodT t1 t2 (numI 0)))
  (test (fulfills? (meth (numT) (numT))
                   (sig (numT) (numT))
                   empty empty)
        #t)
  (test (fulfills? (meth (numT) (objT 'Object))
                   (sig (numT) (numT))
                   empty empty)
        #f)
  (test (fulfills? (meth (intT 'IBool) (intT 'IBool))
                   (sig (intT 'IBool) (intT 'IBool))
                   klasses
                   interfs)
        #t)
  (test (fulfills? (meth (numT) (objT 'True))
                   (sig (numT) (intT 'IBool))
                   klasses
                   interfs)
        #t)
  (test (fulfills? (meth (numT) (objT '3DNumber))
                   (sig (numT) (intT 'INum))
                   klasses
                   interfs)
        #t)
  (test (fulfills? (meth (objT 'Object) (objT '2DNumber))
                   (sig (objT 'Object) (intT 'IBool))
                   klasses
                   interfs)
        #f)
  (test (valid-impl? 'True 'INum klasses interfs)
        #t)
  (test (valid-impl? 'True 'IBool klasses interfs)
        #t)
  (test (valid-impl? '3DNumber 'INum klasses interfs)
        #t)
  (test (valid-impl? '2DNumber 'IBool klasses interfs)
        #f)
  (test (valid-impl? 'SomeClass 'IFoo klasses interfs)
        #t)
  (test (valid-impl? 'True 'IBuz klasses interfs)
        #t)
  ;; classes are obligated to implement all requirements of any superinterface
  ;; of their declared interfaces
  (define klasses2 (append
                    klasses
                    (list (pair 'MissingNumImpl
                                (classT 'Object
                                        '(IBool)
                                        '()
                                        (list (pair '&
                                                    (pair 'arg
                                                          (methodT (intT 'IBool)
                                                                   (intT 'IBool)
                                                                   (thisI)))))))
                          ;; and simply having the required methods isnt enough, the interface
                          ;; or one of its subinterfaces must be named in the class declaration
                          ;; or one of its superclasses
                          (pair 'ImplementsButDoesntName
                                (classT 'ImplButNoName
                                        '()
                                        '()
                                        (list (pair '->num
                                                    (pair 'arg
                                                          (methodT (numT) (numT) (numI 0))))))))))
  (test (valid-impl? 'MissingNumImpl 'IBool klasses2 interfs)
        #f)
  (test (valid-impl? 'ImplButNoName 'INum klasses2 interfs)
        #f))