#lang plait

(require "utils.rkt")

(define-type Exp
  (numE [n : Number])
  (idE [s : Symbol])
  ;; our let is similar to Plait's let*
  ;; e.g. this expression evaluates to 0:
  ;;`{let {[a 1] [b {* -1 a}]} {+ a b}}
  (letE [ids : (Listof Symbol)]
        [exps : (Listof Exp)]
        [body : Exp])
  (plusE [lhs : Exp]
         [rhs : Exp])
  (multE [lhs : Exp]
         [rhs : Exp])
  (thisE)
  (newE [class-name : Symbol]
        [args : (Listof Exp)])
  (getE [obj-expr : Exp]
        [field-name : Symbol])
  (sendE [obj-expr : Exp]
         [method-name : Symbol]
         [arg-expr : Exp])
  (ssendE [obj-expr : Exp]
          [class-name : Symbol]
          [method-name : Symbol]
          [arg-expr : Exp])
  (if0E [tst : Exp]
        [tb : Exp]
        [fb : Exp]))

(define-type Class
  (classC [field-names : (Listof Symbol)]
          ;; a method is a name paired with
          ;; an arg name paired with an expression
          [methods : (Listof (Symbol * (Symbol * Exp)))]))

(module+ test
  ;; this form will be handy for creating classes to use in tests
  (define (mk-mthd [method-name : Symbol] [arg-name : Symbol] [body : Exp])
    (values method-name
            (values arg-name body))))

(define objC (classC '() '()))

(define-type Value
  (numV [n : Number])
  (objV [class-name : Symbol]
        [field-values : (Listof Value)]))

(module+ test
  (print-only-errors #t))

;; ----------------------------------------

;; it's convenient to use a form compatible with `find`
(define-type-alias Env (Listof (Symbol * Value)))
(define mt-env '())
(define ext-env cons)
(define (bind [name : Symbol] [v : Value])
  (values name v))

(module+ test
  (test (ext-env (values 'a (numV 1)) mt-env)
        (list (values 'a (numV 1))))
  (test (find (list (bind 'x (objV 'Object '())))
              'x)
        (objV 'Object '())))

(define (findC [l : (Listof (Symbol * Class))] [name : Symbol]) : Class
  (if (symbol=? name 'Object)
      objC
      (find l name)))

(module+ test
  (test (findC '() 'Object)
        objC)
  (test (findC (list (values 'Object
                             (classC '(x y z) '())))
               'Object)
        objC)
  (test (findC (list (values 'Foo
                             (classC '(bar baz) '())))
               'Foo)
        (classC '(bar baz) '())))

;; ----------------------------------------

(define interp : (Exp (Listof (Symbol * Class)) Value Env -> Value)
  (lambda (a classes this-val env)
    (local [(define (recur expr)
              (interp expr classes this-val env))
            (define (recur-with with-env expr)
              (interp expr classes this-val with-env))]
      (type-case Exp a
        [(numE n) (numV n)]
        [(idE s) (find env s)]
        [(letE ns es body)
         (recur-with
          (foldl2 (lambda (n e nv)
                    (ext-env
                     (bind n ; this recur-with call is what makes it let*
                           (recur-with nv e))
                     nv))
                  env
                  ns
                  es)
          body)]
        [(plusE l r) (num+ (recur l) (recur r))]
        [(multE l r) (num* (recur l) (recur r))]
        [(thisE) this-val]
        [(newE class-name field-exprs)
         (local [(define c (findC classes class-name))
                 (define vals (map recur field-exprs))]
           (if (= (length vals) (length (classC-field-names c)))
               (objV class-name vals)
               (error 'interp "wrong field count")))]
        [(getE obj-expr field-name)
         (type-case Value (recur obj-expr)
           [(objV class-name field-vals)
            (type-case Class (findC classes class-name)
              [(classC field-names methods)
               (let/cc k
                 (foldl2 (lambda (n v acc)
                           (if (symbol=? n field-name)
                               (k v)
                               acc))
                         (numV 0) ; dummy
                         field-names
                         field-vals))])]
           [else (error 'interp "not an object")])]
        [(sendE obj-expr method-name arg-expr)
         (local [(define obj (recur obj-expr))
                 (define arg-val (recur arg-expr))]
           (type-case Value obj
             [(objV class-name field-vals)
              (call-method class-name method-name classes
                           obj arg-val
                           env)]
             [else (error 'interp "not an object")]))]
        [(ssendE obj-expr class-name method-name arg-expr)
         (local [(define obj (recur obj-expr))
                 (define arg-val (recur arg-expr))]
           (call-method class-name method-name classes
                        obj arg-val
                        env))]
        [(if0E tst tb fb)
         (type-case Value (recur tst)
           [(numV n) (if (= 0 n)
                         (recur tb)
                         (recur fb))]
           [else (error 'interp "not a number")])]))))

(module+ test
  ;; convenience forms for simple tests
  (define (i [e : Exp])
    (interp e empty (objV 'Foo empty) mt-env))
  (define (i-with [e : Exp] [env : Env])
    (interp e empty (objV 'Foo empty) env)))

(define (call-method class-name method-name classes
                     obj arg-val env)
  (type-case Class (findC classes class-name)
    [(classC field-names methods)
     (let* ([method (find methods method-name)]
            [arg-name (fst method)]
            [body-expr (snd method)])
       (type-case Value obj
         [(objV c-name field-vals)
          (interp body-expr
                  classes
                  obj
                  (ext-env (bind arg-name arg-val)
                           (foldl2-until (lambda (f v nv)
                                           (ext-env
                                            (bind f v)
                                            nv))
                                         mt-env ; TODO should be mt-env or else we've accidentally done dynamic scoping
                                         field-names
                                         field-vals)))]
         [else (error 'interp (string-append (to-string obj) " not an object"))]))]))

(module+ test
  (define BeagleClass
    (pair 'beagle
          (classC '(a b c) (list (pair 'sum
                                       (pair 'arg
                                             (plusE (idE 'a)
                                                    (plusE (idE 'b) (idE 'c)))))
                                 (pair 'shadowed-sum
                                       (pair 'a
                                             (plusE (idE 'a)
                                                    (plusE (idE 'b) (idE 'c)))))))))
  
  (test (interp (sendE (newE 'beagle
                             (list (numE 1)
                                   (numE 2)
                                   (numE 3)))
                       'sum (numE 0))
                (list BeagleClass)
                (objV 'Object empty)
                mt-env)
        (numV 6))
  (test (interp (sendE (newE 'beagle
                             (list (numE 1)
                                   (numE 2)
                                   (numE 3)))
                       'shadowed-sum
                       (numE -1))
                (list BeagleClass)
                (objV 'Object empty)
                mt-env)
        (numV 4)))

(define (num-op [op : (Number Number -> Number)]
                [op-name : Symbol] 
                [x : Value]
                [y : Value]) : Value
  (cond
    [(and (numV? x) (numV? y))
     (numV (op (numV-n x) (numV-n y)))]
    [else (error 'interp "not a number")]))

(define (num+ x y) (num-op + '+ x y))
(define (num* x y) (num-op * '* x y))

;; ----------------------------------------
;; Examples

(module+ test
  (test (i (if0E (numE 0) (numE 1) (numE -1)))
        (numV 1))
  (test (i (if0E (plusE (numE 0) (numE 98))
                 (multE (numE 3) (numE 2))
                 (newE 'Object '())))
        (objV 'Object '()))
  (test/exn (i (if0E (newE 'Object '())
                     (numE 0)
                     (numE 0)))
            "not a number")
  
  ;; included
  (define posn-class
    (values 'Posn
            (classC 
             (list 'x 'y)
             (list (mk-mthd 'mdist
                            '_
                            (plusE (getE (thisE) 'x) (getE (thisE) 'y)))
                   (mk-mthd 'addDist
                            'arg
                            (plusE (sendE (thisE) 'mdist (numE 0))
                                   (sendE (idE 'arg) 'mdist (numE 0))))
                   (mk-mthd 'addX
                            'foo
                            (plusE (getE (thisE) 'x) (idE 'foo)))
                   (mk-mthd 'multY
                            'bar
                            (multE (idE 'bar) (getE (thisE) 'y)))
                   (mk-mthd 'factory12
                            '_
                            (newE 'Posn (list (numE 1) (numE 2))))))))

  (define posn3D-class
    (values 'Posn3D
            (classC 
             (list 'x 'y 'z)
             (list (mk-mthd 'mdist
                            'arg
                            (plusE (getE (thisE) 'z)
                                   (ssendE (thisE) 'Posn 'mdist (idE 'arg))))
                   (mk-mthd 'addDist
                            'arg
                            (ssendE (thisE) 'Posn 'addDist (idE 'arg)))))))

  (define posn27 (newE 'Posn (list (numE 2) (numE 7))))
  (define posn531 (newE 'Posn3D (list (numE 5) (numE 3) (numE 1))))

  (define (interp-posn a)
    (interp a (list posn-class posn3D-class) (numV -1) '())))

;; ----------------------------------------

(module+ test
  ;; letE
  (test (i (letE '(x)
                 (list (numE 0))
                 (idE 'x)))
        (numV 0))
  (test (i (letE '(x y z)
                 (list (numE 1)
                       (numE 2)
                       (numE 3))
                 (plusE (idE 'x)
                        (plusE (idE 'y)
                               (idE 'z)))))
        (numV 6))
  ;; let bindings should shadow outer bindings
  (test (i-with (letE '(foo)
                      (list (numE 8.3))
                      (idE 'foo))
                (list (bind 'foo (numV -90000))))
        (numV 8.3))

  ;; let behaves like let* (to my understanding)
  (test (i (letE '(x y)
                 (list (numE 2) ; x = 2
                       (plusE (idE 'x)
                              (numE 2))) ; y = x + 2
                 (plusE (idE 'x)
                        (idE 'y))))
        (numV 6))

  ;; idE
  (test (interp (idE 'x)
                empty
                (objV 'Foo empty)
                (list (bind 'x (numV 10))))
        (numV 10))

  ;; included
  (test (interp (numE 10) 
                empty (objV 'Object empty)
                mt-env)
        (numV 10))
  (test (interp (plusE (numE 10) (numE 17))
                empty (objV 'Object empty)
                mt-env)
        (numV 27))
  (test (interp (multE (numE 10) (numE 7))
                empty (objV 'Object empty)
                mt-env)
        (numV 70))

  (test (interp-posn (newE 'Posn (list (numE 2) (numE 7))))
        (objV 'Posn (list (numV 2) (numV 7))))

  (test (interp-posn (sendE posn27 'mdist (numE 0)))
        (numV 9))

  (test (interp-posn (sendE posn27 'addX (numE 10)))
        (numV 12))

  (test (interp-posn (sendE (ssendE posn27 'Posn 'factory12 (numE 0))
                            'multY
                            (numE 15)))
        (numV 30))

  (test (interp-posn (sendE posn531 'addDist posn27))
        (numV 18))

  (test/exn (interp-posn (plusE (numE 1) posn27))
            "not a number")
  (test/exn (interp-posn (getE (numE 1) 'x))
            "not an object")
  (test/exn (interp-posn (sendE (numE 1) 'mdist (numE 0)))
            "not an object")
  (test/exn (interp-posn (ssendE (numE 1) 'Posn 'mdist (numE 0)))
            "not an object")
  (test/exn (interp-posn (newE 'Posn (list (numE 0))))
            "wrong field count"))
