#lang plait

;; Make all "class.rkt" definitions available here, where
;; the "class.rkt" file must be in the same directory
;; as this one:
(require "class.rkt"
         "utils.rkt")

(module+ test
  (print-only-errors #t))

(define-type ExpI
  (numI [n : Number])
  (plusI [lhs : ExpI]
         [rhs : ExpI])
  (multI [lhs : ExpI]
         [rhs : ExpI])
  (thisI)
  (newI [class-name : Symbol]
        [args : (Listof ExpI)])
  (getI [obj-expr : ExpI]
        [field-name : Symbol])
  (sendI [obj-expr : ExpI]
         [method-name : Symbol]
         [arg-expr : ExpI])
  (superI [method-name : Symbol]
          [arg-expr : ExpI])
  (idI [s : Symbol])
  (letI [ns : (Listof Symbol)]
        [es : (Listof ExpI)]
        [body : ExpI])
  (if0I [tst : ExpI]
        [tb : ExpI]
        [fb : ExpI]))

(define-type ClassI
  (objI)
  (classI [super-name : Symbol]
          [field-names : (Listof Symbol)]
          ; A method is: (METHOD-NAME * (ARG-NAME * BODY))
          [methods : (Listof (Symbol * (Symbol * ExpI)))]))

(module+ test
  ;; convenience functions for constructing tests
  (define (mk-mthd [method-name : Symbol] [arg-name : Symbol] [body : 'a])
    (values method-name
            (values arg-name body)))
  (define (mk-mthdC name arg [body : Exp])
    (mk-mthd name arg body))
  (define (mk-mthdI name arg [body : ExpI])
    (mk-mthd name arg body))

  (test (mk-mthd 'a 'b 'c)
        (values 'a (values 'b 'c)))
  (test (mk-mthd 'a 'b (thisE))
        (mk-mthdC 'a 'b (thisE)))
  (test (mk-mthd 'a 'b (thisI))
        (mk-mthdI 'a 'b (thisI))))


;; ----------------------------------------

(define (exp-i->c [a : ExpI] [super-name : Symbol]) : Exp
  (local [(define (recur expr)
            (exp-i->c expr super-name))]
    (type-case ExpI a
      [(idI n) (idE n)]
      [(numI n) (numE n)]
      [(plusI l r) (plusE (recur l) (recur r))]
      [(multI l r) (multE (recur l) (recur r))]
      [(thisI) (thisE)]
      [(newI class-name field-exprs)
       (newE class-name (map recur field-exprs))]
      [(getI expr field-name)
       (getE (recur expr) field-name)]
      [(sendI expr method-name arg-expr)
       (sendE (recur expr)
              method-name
              (recur arg-expr))]
      [(superI method-name arg-expr)
       (ssendE (thisE)
               super-name
               method-name
               (recur arg-expr))]
      [(letI ns es bdy)
       (letE ns
             (map recur es)
             (recur bdy))]
      [(if0I tst tb fb)
       (if0E (recur tst) (recur tb) (recur fb))])))

(module+ test
  ;;if0
  (test (exp-i->c (if0I (numI 0) (numI 1) (numI 2)) 'whatever)
        (if0E (numE 0) (numE 1) (numE 2)))
  ;; idI
  (test (exp-i->c (idI 'x) '_)
        (idE 'x))
  ;; letI
  (test (exp-i->c (letI '(x)
                        (list (superI 'foo (numI 0)))
                        (idI 'x))
                  'bar)
        (letE '(x)
              (list (ssendE (thisE) 'bar 'foo (numE 0)))
              (idE 'x)))
  (test (exp-i->c (numI 10) 'Object)
        (numE 10))
  (test (exp-i->c (plusI (numI 10) (numI 2)) 'Object)
        (plusE (numE 10) (numE 2)))
  (test (exp-i->c (multI (numI 10) (numI 2)) 'Object)
        (multE (numE 10) (numE 2)))
  (test (exp-i->c (thisI) 'Object)
        (thisE))
  (test (exp-i->c (newI 'Object (list (numI 1))) 'Object)
        (newE 'Object (list (numE 1))))
  (test (exp-i->c (getI (numI 1) 'x) 'Object)
        (getE (numE 1) 'x))
  (test (exp-i->c (sendI (numI 1) 'mdist (numI 2)) 'Object)
        (sendE (numE 1) 'mdist (numE 2)))
  (test (exp-i->c (superI 'mdist (numI 2)) 'Posn)
        (ssendE (thisE) 'Posn 'mdist (numE 2))))

;; ----------------------------------------

(define (class-i->c-not-flat [c : ClassI]) : Class
  (type-case ClassI c
    [(objI) objC]
    [(classI super-name field-names methods)
     (classC
      field-names
      (map (lambda (m)
             (values (fst m)
                     (values (fst (snd m))
                             (exp-i->c (snd (snd m)) super-name))))
           methods))]))

(module+ test
  (test (class-i->c-not-flat (objI))
        objC)
  
  (define posn3d-mdist-i-method
    (mk-mthdI 'mdist
              'arg
              (plusI (getI (thisI) 'z)
                     (superI 'mdist (idI 'arg)))))
  (define posn3d-mdist-c-method
    (mk-mthdC 'mdist
              'arg
              (plusE (getE (thisE) 'z)
                     (ssendE (thisE) 'Posn 'mdist (idE 'arg)))))

  (define posn3d-i-class 
    (values 'Posn3D
            (classI
             'Posn
             (list 'z)
             (list posn3d-mdist-i-method))))
  (define posn3d-c-class-not-flat
    (values 'Posn3D
            (classC (list 'z)
                    (list posn3d-mdist-c-method))))

  (test (class-i->c-not-flat (snd posn3d-i-class))
        (snd posn3d-c-class-not-flat)))

;; ----------------------------------------

(define (findI [i-classes : (Listof (Symbol * ClassI))] [name : Symbol])
  (if (symbol=? name 'Object)
      (objI)
      (find i-classes name)))

(define (flatten-class [name : Symbol]
                       [classes-not-flat : (Listof (Symbol * Class))] 
                       [i-classes : (Listof (Symbol * ClassI))]) : Class
  (type-case Class (findC classes-not-flat name)
    [(classC field-names methods)
     (type-case Class (flatten-super name classes-not-flat i-classes)
       [(classC super-field-names super-methods)
        (classC
         (add-fields super-field-names field-names)
         (add/replace-methods super-methods methods))])]))

(define (flatten-super [name : Symbol]
                       [classes-not-flat : (Listof (Symbol * Class))] 
                       [i-classes : (Listof (Symbol * ClassI))]) : Class
  (type-case ClassI (findI i-classes name)
    [(objI) objC]
    [(classI super-name field-names i-methods)
     (flatten-class super-name
                    classes-not-flat
                    i-classes)]))

(module+ test
  (define posn-i-class
    (values
     'Posn
     (classI 'Object
             (list 'x 'y)
             (list (mk-mthdI 'mdist
                             '_
                             (plusI (getI (thisI) 'x)
                                    (getI (thisI) 'y)))
                   (mk-mthdI 'addDist
                             'arg
                             (plusI (sendI (thisI) 'mdist (numI 0))
                                    (sendI (idI 'arg) 'mdist (numI 0))))))))
  (define addDist-c-method
    (mk-mthdC 'addDist
              'arg
              (plusE (sendE (thisE) 'mdist (numE 0))
                     (sendE (idE 'arg) 'mdist (numE 0)))))
  (define posn-c-class-not-flat
    (values
     'Posn
     (classC (list 'x 'y)
             (list (mk-mthdC 'mdist
                             '_
                             (plusE (getE (thisE) 'x)
                                    (getE (thisE) 'y)))
                   addDist-c-method))))
  (define posn3d-c-class
    (values 'Posn3D
            (classC (list 'x 'y 'z)
                    (list posn3d-mdist-c-method
                          addDist-c-method))))

  (test (flatten-class 'Posn3D
                       (list posn-c-class-not-flat
                             posn3d-c-class-not-flat)
                       (list posn-i-class
                             posn3d-i-class))
        (snd posn3d-c-class)))

;; ----------------------------------------

(define add-fields append)

(define (add/replace-methods [methods : (Listof (Symbol * (Symbol * Exp)))]
                             [new-methods : (Listof (Symbol * (Symbol * Exp)))])
  : (Listof (Symbol * (Symbol * Exp)))
  (cond
    [(empty? new-methods) methods]
    [else (add/replace-methods
           (add/replace-method methods (first new-methods))
           (rest new-methods))]))

(define (add/replace-method [methods : (Listof (Symbol * (Symbol * Exp)))] 
                            [new-method : (Symbol * (Symbol * Exp))])
  : (Listof (Symbol * (Symbol * Exp)))
  (cond
    [(empty? methods) (list new-method)]
    [else
     (if (equal? (fst (first methods))
                 (fst new-method))
         (cons new-method (rest methods))
         (cons (first methods) 
               (add/replace-method (rest methods)
                                   new-method)))]))

(module+ test
  (test (add-fields (list 'x 'y) (list 'z))
        (list 'x 'y 'z))

  (test (add/replace-methods empty empty)
        empty)
  (test (add/replace-methods empty (list (values 'm (values 'foo (numE 0)))))
        (list (values 'm (values 'foo (numE 0)))))
  (test (add/replace-methods (list (values 'm (values '_ (numE 0)))) empty)
        (list (values 'm (values '_ (numE 0)))))
  (test (add/replace-methods (list (values 'm (values '_ (numE 0))))
                             (list (values 'm (values '_ (numE 1)))))
        (list (values 'm (values '_ (numE 1)))))
  (test (add/replace-methods (list (values 'm (values '_ (numE 0)))
                                   (values 'n (values '_ (numE 2))))
                             (list (values 'm (values '_ (numE 1)))))
        (list (values 'm (values '_ (numE 1)))
              (values 'n (values '_ (numE 2)))))
  (test (add/replace-methods (list (values 'm (values '_ (numE 0))))
                             (list (values 'm (values '_ (numE 1)))
                                   (values 'n (values '_ (numE 2)))))
        (list (values 'm (values '_ (numE 1)))
              (values 'n (values '_ (numE 2)))))

  (test (add/replace-method (list (values 'm (values '_ (numE 0))))
                            (values 'm (values '_ (numE 1))))
        (list (values 'm (values '_ (numE 1)))))
  (test (add/replace-method (list (values 'm (values '_ (numE 0))))
                            (values 'n (values '_ (numE 2))))
        (list (values 'm (values '_ (numE 0)))
              (values 'n (values '_ (numE 2))))))

;; ----------------------------------------

(define (interp-i [i-a : ExpI] [i-classes : (Listof (Symbol * ClassI))]) : Value
  (local [(define a (exp-i->c i-a 'Object))
          (define classes (classes-i->c-flat i-classes))]
    (interp a classes (objV 'Object empty) mt-env)))

(define (classes-i->c-flat [klasses : (Listof (Symbol * ClassI))]) : (Listof (Symbol * Class))
  (local [(define classes-not-flat
            (map (lambda (i)
                   (values (fst i)
                           (class-i->c-not-flat (snd i))))
                 klasses))
          (define classes
            (map (lambda (c)
                   (let ([name (fst c)])
                     (values name
                             (flatten-class name classes-not-flat klasses))))
                 classes-not-flat))]
    classes))

(module+ test
  (test (interp-i (if0I (numI 0) (newI 'Object '()) (newI 'Foo (list (numI -1))))
                  (list (pair 'Foo (classI 'Object '(x) '()))))
        (objV 'Object '()))
  (test (interp-i (if0I (numI 1) (newI 'Object '()) (newI 'Foo (list (numI -1))))
                  (list (pair 'Foo (classI 'Object '(x) '()))))
        (objV 'Foo (list (numV -1))))
  (test (interp-i (numI 0) empty)
        (numV 0))

  (test (interp-i
         (sendI (newI 'Posn3D (list (numI 5) (numI 3) (numI 1)))
                'addDist
                (newI 'Posn (list (numI 2) (numI 7))))
         (list posn-i-class
               posn3d-i-class))
        (numV 18)))
