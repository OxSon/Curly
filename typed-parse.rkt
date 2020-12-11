#lang plait

(require "utils.rkt"
         "class.rkt"
         "inherit.rkt"
         "types.rkt"
         "typecheck.rkt"
         "parse-ext.rkt")

(module+ test
  (print-only-errors #t))

#|
Examples in this file run REALLY slowly, especially when test coverage is enabled.

Is that a consequence of using macros and having parse expanders?
If so, is there something I can do to write more efficient macros,
or more efficient expanders?

If not, what could be the reason? Anything here look obviously inefficient?

Also, it seems like macros can really screw up error messages. For example,
I had a bug where my expander was expanding classes incorrectly and leading
to an eventual call to `parse-t-method*` to fail with "invalid input",
but the error message said nothing about a test failing or anything,
it just pointed me to parse-ext.rkt like this:
XX parse-ext.rkt:155:10: parse-t-method: invalid input
|#

;; ----------------------------------------

(define standard-expander
  (lambda (s)
    (cond
      ;; our sole expression syntactic sugar at the moment...
      ;; its also not very useful but it works as a POC to myself
      [(s-exp-match? `{where ANY {[SYMBOL ANY] ...}} s)
       (some `{let ,(third (s-exp->list s))
                ,(second (s-exp->list s))})]
      ;; there must be a better way to do this
      ;; without having to write three patterns for classes?
      ;; (i.e. missing superclass name, missing impls list, both missing)
      
      ; missing superclass name = class extends object
      [(s-exp-match? `{class SYMBOL :: {SYMBOL ...} {ANY ...} ANY ...} s)
       (let ([sl (s-exp->list s)])
         (some `{class ,(second sl) <= Object :: ,(fourth sl)
                  ,(fourth (rest sl))
                  ,@(rest (rest (rest (rest (rest sl)))))}))]
      ; missing impls list = class implements no interfaces (directly)
      [(s-exp-match? `{class SYMBOL <= SYMBOL {ANY ...} ANY ...} s)
       (let ([sl (s-exp->list s)])
         (some `{class ,(second sl) <= ,(fourth sl) :: {}
                  ,(fourth (rest sl))
                  ,@(rest (rest (rest (rest (rest sl)))))}))]
      ; both missing = class extends object and directly implements no interfaces
      [(s-exp-match? `{class SYMBOL {ANY ...} ANY ...} s)
       (let ([sl (s-exp->list s)])
         (some `{class ,(second sl) <= Object :: {}
                  ,(third sl)
                  ,@(rest (rest (rest sl)))}))]
      ;; missing superinterfaces list = interface extends no other interfaces
      [(and (s-exp-match? `{interface SYMBOL ANY ...} s)
            (not (s-exp-match? `{interface SYMBOL <= ANY ...} s)))
       (some `{interface ,(second (s-exp->list s)) <= {}
                ,@(rest (rest (s-exp->list s)))})]
      [else (none)])))

;; parse-sig and parse-type don't actually use anything
;; in the expander (no patterns will match) at the moment,
;; but i figured I'd include them while I'm at it
;; in case I come up with an idea later on
(define-values (parse
                parse-t-class parse-t-method parse-t-field
                parse-sig parse-interface
                parse-type)
  (let ([std standard-expander])
    (values (lambda (s)
              (parse* s std))
            (lambda (s tenv)
              (parse-t-class* s std tenv))
            (lambda (s tenv)
              (parse-t-method* s std tenv))
            (lambda (s tenv)
              (parse-t-field* s std tenv))
            (lambda (s tenv)
              (parse-sig* s std tenv))
            (lambda (s tenv)
              (parse-interface* s std tenv))
            (lambda (s tenv)
              (parse-type* s std tenv)))))

(module+ test
  (define noop (lambda (s) (none)))
  ;------ exps
  (test (parse `foo)
        (idI 'foo))
  (test (parse `{where x {[x 3]}})
        (parse* `{let {[x 3]} x} noop))
  (test (parse `{where {send wally eat {* x {* y z}}}
                       {[wally {new Dog 18}]
                        [x 3] [y 4] [z 5]}})
        (parse* `{let {[wally {new Dog 18}]
                       [x 3] [y 4] [z 5]}
                   {send wally eat {* x {* y z}}}}
                noop))

  ;------ methods

  (test (parse-t-method `[f {[arg : num]} : num 0] mt-env)
        (pair 'f (pair 'arg (methodT (numT) (numT) (numI 0)))))
  (test/exn (parse-t-method `[f {[arg : num]} 0] empty)
            "invalid input")

  ;------ fields
  (test (parse-t-field `[x : Foo] (list (tbind 'Foo (intT 'Foo))))
        (pair 'x (intT 'Foo)))

  ;------ sigs
  (test (parse-sig `[g : num -> Foo] (list (tbind 'Foo (objT 'Foo))))
        (pair 'g (sig (numT) (objT 'Foo))))

  ;------ types
  (test (parse-type `num empty)
        (numT))
  (test (parse-type `Foo (list (tbind 'Foo (objT 'Foo))))
        (objT 'Foo))
  (test/exn (parse-type `Bar empty)
            "not found")
  
  ;------ classes
  ; missing impls
  (test (parse-t-class `{class Foo <= Bar {}} empty)
        (parse-t-class* `{class Foo <= Bar :: {} {}} noop empty))
  ; missing super class
  (test (parse-t-class `{class Foo :: {i1 i2 i3}
                          {[x : num] [y : num] [z : num]}
                          [f {[a : num]} : Foo this]
                          [g {[b : num]} : num {* b b}]}
                       (list (tbind 'Foo (objT 'Foo))))
        (parse-t-class* `{class Foo <= Object :: {i1 i2 i3}
                           {[x : num] [y : num] [z : num]}
                           [f {[a : num]} : Foo this]
                           [g {[b : num]} : num {* b b}]}
                        noop
                        (list (tbind 'Foo (objT 'Foo)))))
  ; missing both
  (test (parse-t-class `{class Foo {} [f {[arg : num]} : num {* -1 num}]} empty)
        (parse-t-class* `{class Foo <= Object :: {}
                           {}
                           [f {[arg : num]} : num {* -1 num}]}
                        noop empty))

  ;----- interfaces
  (test (parse-interface `{interface Foo [f : num -> num]} empty)
        (parse-interface* `{interface Foo <= {} [f : num -> num]} noop empty))
  (test (parse-interface `{interface Foo <= {a b c}} empty)
        (pair 'Foo (interf '(a b c) '()))))

(define (to-s-exp [v : Value] [t-classes : ClassList])
  (let ([flat-classes (classes-i->c-flat
                       (map (lambda (klass)
                              (pair (fst klass)
                                    (strip-types (snd klass))))
                            t-classes))])
    (to-s-exp* v flat-classes)))

(define (to-s-exp* [v : Value] [class-list : (Listof (Symbol * Class))])
  (type-case Value v
    [(numV n) (number->s-exp n)]
    [(objV c-name vals)
     (if (symbol=? c-name 'Object)
         `{OBJECT}
         (let* ([field-names (classC-field-names (find class-list c-name))]
                [fields (map2 (lambda ([name : Symbol] [val : Value])
                                `[,(symbol->s-exp name) = ,(to-s-exp* val class-list)])
                              field-names
                              vals)])
           `{,(symbol->s-exp c-name) with {,@fields}}))]))

(module+ test
  (test (to-s-exp (numV 394920) '())
        `394920)
  (define Foo (parse-t-class `{class Foo <= Object
                                {[x : num] [y : num] [friend : Object]}}
                             empty))
  (test (to-s-exp (objV 'Foo (list (numV 1) (numV 2) (objV 'Object '())))
                  (list Foo))
        `{Foo with {[x = 1] [y = 2] [friend = {OBJECT}]}}))

(define (run-prog [interfs : (Listof S-Exp)]
                  [classes : (Listof S-Exp)]
                  [main : S-Exp]) : S-Exp
  (let* ([step (lambda ([ctor : (Symbol -> Type)])
                 (lambda (i/c env)
                   (let ([name (identifier! (second (s-exp->list i/c)))])
                     (ext-env-uniq (tbind name (ctor name)) env))))]
         [tenv (foldl (step intT)
                      ; initial acc for outer fold is result of inner fold
                      (foldl (step objT) empty classes)
                      interfs)]
         [map-with (lambda (env f l)
                     (map (lambda (a)
                            (f a env))
                          l))]
         [class-list (map-with tenv parse-t-class classes)]
         [interf-list (map-with tenv parse-interface interfs)]
         [main-exp (parse main)])
    (begin
      (typecheck main-exp class-list interf-list tenv)
      (to-s-exp (interp-t main-exp class-list) class-list))))

(module+ test
  (test (run-prog (list `{interface i})
                  (list `{class a <= Object
                           {[x : num]}}
                        `{class b <= a :: {i}
                           {}
                           [invert-x {[a : a]} : num {if0 {get a x} 1 0}]})
                  `{let {[b 3]
                         [a 0]}
                     {send {new b b} invert-x {new a a}}})
        `1)
  (test (run-prog
         (list
          `{interface animal
             [eat : num -> animal]})
         (list
          `{class Human :: {animal}
             {[weight : num]}
             [eat {[eatee : num]} : Human
                  ; would be more interesting w/ assignment
                  {new Human {+ 1 {get this weight}}}]}
          `{class Cat :: {animal} {}
             [eat {[eatee : num]} : animal
                  this]}
          `{class Tiger <= Cat
             {[weight : num]}
             [eat {[eatee : num]} : Tiger
                  {new Tiger {+ {get this weight}
                                eatee}}]})
         `{let {[h {new Human 170}]
                [t {new Tiger 350}]}
            {get {send t eat
                       {get h weight}}
                 weight}})
        (number->s-exp (+ 170 350)))

  (test/exn (run-prog
             (list `{interface i
                      [f : Object -> num]})
             (list `{class A
                      {}
                      [f {[arg : num]} : Object {new A}]}
                   `{class B <= A :: {i}
                      {}
                      [f {[arg : Object]} : num 0]})
             `{send {new B} f {new B}})
            "bad override")
  (let ([klasses (list `{class a
                          {}
                          [f {[arg : num]} : a {new a}]}
                       `{class b <= a :: {i}
                          {}
                          [f {[arg : num]} : b {new b}]})])
    (test (run-prog
           (list `{interface i
                    [f : num -> Object]})
           klasses
           `{send {new b} f 0})
          (to-s-exp (objV 'b '()) (map (lambda (klass)
                                         (parse-t-class
                                          klass
                                          (list (tbind 'a (objT 'a))
                                                (tbind 'b (objT 'b))
                                                (tbind 'i (intT 'i)))))
                                       klasses)))))


(define (test-prog [classes/interfs : (Listof S-Exp)] [main : S-Exp]) : S-Exp
  (let* ([is-a? (lambda (keyword)
                  (lambda (s)
                    (s-exp-match? keyword (first (s-exp->list s)))))]
         [is-class? (is-a? `class)]
         [is-interf? (is-a? `interface)]
         [class-list (filter is-class? classes/interfs)]
         [interf-list (filter is-interf? classes/interfs)]
         [s (run-prog interf-list class-list main)])
    (cond
      [(s-exp-match? `{SYMBOL with {ANY ...}} s)
       `{obj ,(first (s-exp->list s))}]
      [else s])))

(module+ test
  (define c/i-list (list `{class a
                            {[x : num]}}
                         `{class b <= a
                            {}
                            [f {[x : num]} : num
                               {+ x {get this x}}]}
                         `{class c <= b :: {i} {}}
                         `{interface i
                            [f : num -> num]}))
  (test (test-prog c/i-list `{send {new c 1} f 1})
        `2)
  (test (test-prog c/i-list `{new c 69})
        `{obj c})
  (test (test-prog (list `{interface Number [->num : num -> num]}
                         `{interface Bool <= {Number}
                            [& : Bool -> Bool]
                            [|| : Bool -> Bool]
                            [^ : Bool -> Bool]
                            [~ : Object -> Bool]}
                         `{class True :: {Bool}
                            {}
                            [->num {[_ : num]} : num 0]
                            [& {[b : Bool]} : Bool b]
                            [|| {[b : Bool]} : Bool this]
                            [^ {[b : Bool]} : Bool
                               {if0 {send b ->num 1}
                                    {new False}
                                    this}]
                            [~ {[_ : Object]} : Bool {new False}]}
                         `{class False :: {Bool}
                            {}
                            [->num {[_ : num]} : num 1]
                            [|| {[b : Bool]} : Bool b]
                            [& {[b : Bool]} : Bool this]
                            [^ {[b : Bool]} : Bool b]
                            [~ {[_ : Object]} : Bool {new True}]})
                   `{let {[true {new True}]
                          [false {new False}]}
                      {send {send {send false ^ true}
                                  &
                                  true}
                            ->num
                            0}})
        `0)
  ;; fields directly referenced
  (test (test-prog (list `{class Beagle
                            {[x : num] [y : num]}
                            [sum {[z : num]} : num {+ x {+ y z}}]})
                   `{send {new Beagle 1 2} sum 3})
        `6)
  ;; arg name shadows fields
  (test (test-prog (list `{class Beagle
                            {[x : num] [y : num]}
                            [sum {[x : num]} : num {+ x y}]})
                   `{send {new Beagle 1 2} sum 3})
        `5)
  ;; local bindings shadow fields
  (test (test-prog (list `{class Beagle
                            {[x : num] [y : num]}
                            [sum {[x : num]} : num {let {[x 0] [y 0]}
                                                     {+ x y}}]})
                   `{send {new Beagle 1 2} sum 3})
        `0))