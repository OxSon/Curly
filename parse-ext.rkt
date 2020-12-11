#lang plait

(require "utils.rkt"
         "class.rkt"
         "inherit.rkt"
         "types.rkt")

(module+ test
  (print-only-errors #t))

;------ some helpers ----------------

(define (map-with env xpnd f l)
  (map (lambda (a)
         (f a xpnd env))
       l))

(define (find-type [tenv : T-Env] [t-name : S-Exp])
  (if (s-exp-match? `Object t-name)
      (objT 'Object)
      (find tenv (s-exp->symbol t-name))))

(define (ext-env-uniq [binding : (Symbol * Type)] [tenv : (Listof (Symbol * Type))])
  (if (member (fst binding) (map fst tenv))
      (error 'parse (string-append "duplicate type name: "
                                   (to-string (snd binding))))
      (ext-env binding tenv)))

(module+ test
  (test (ext-env-uniq (pair 'x (numT)) mt-env)
        (list (pair 'x (numT))))
  (test/exn (ext-env-uniq (pair 'x (numT)) (list (pair 'x (objT 'x))))
            "duplicate type name"))

;--------------------------------------

;; Couldnt figure out how to have it handle the not-always-there t-env
;; without using an ellips, since using an ellipse forces me to
;; stick the t-env into the call to xpnd which is not right.
;; This is kinda repititous though, im sure there is a cleaner way to do this?
(define-syntax def*
  (syntax-rules ()
    [(def* (f s xpnd)
       bdy)
     (define (f s xpnd)
       (type-case (Optionof 's) (xpnd s)
         [(some e) (f e xpnd)]
         [(none) bdy]))]
    [(def* (f s xpnd tenv)
       bdy)
     (define (f s xpnd tenv)
       (type-case (Optionof 's) (xpnd s)
         [(some e) (f e xpnd tenv)]
         [(none) bdy]))]))

;; another example of macros not behaving correctly in test modules.
;; It gave me an "undefined: example*" error.
(def* (example* s xpnd)
  (cond
    [(s-exp-match? `contrived s) (list (s-exp->symbol s))]
    [else '(nope)]))

(define-type-alias Expander (S-Exp -> (Optionof S-Exp)))

(module+ test
  (test (example* `before (lambda (s)
                            (if (s-exp-match? `before s)
                                (some `contrived)
                                (none))))
        '(contrived)))

(parse* : (S-Exp Expander -> ExpI))
(def* (parse* s expand)
  (cond
    [(s-exp-match? `NUMBER s) (numI (s-exp->number s))]
    [(s-exp-match? `this s) (thisI)]
    ;; note that the following clause (for identifiers)
    ;; must come after any reserved keyword clauses if applicable
    [(s-exp-match? `SYMBOL s) (idI (identifier! s))]
    [(s-exp-match? `{+ ANY ANY} s)
     (plusI (parse* (second (s-exp->list s)) expand)
            (parse* (third (s-exp->list s)) expand))]
    [(s-exp-match? `{* ANY ANY} s)
     (multI (parse* (second (s-exp->list s)) expand)
            (parse* (third (s-exp->list s)) expand))]
    [(s-exp-match? `{new SYMBOL ANY ...} s)
     (newI (identifier! (second (s-exp->list s)))
           (map (lambda (s)
                  (parse* s expand))
                (rest (rest (s-exp->list s)))))]
    [(s-exp-match? `{get ANY SYMBOL} s)
     (getI (parse* (second (s-exp->list s)) expand)
           (identifier! (third (s-exp->list s))))]
    [(s-exp-match? `{send ANY SYMBOL ANY} s)
     (sendI (parse* (second (s-exp->list s)) expand)
            (identifier! (third (s-exp->list s)))
            (parse* (fourth (s-exp->list s)) expand))]
    [(s-exp-match? `{super SYMBOL ANY} s)
     (superI (s-exp->symbol (second (s-exp->list s)))
             (parse* (third (s-exp->list s)) expand))]
    [(s-exp-match? `{let {[SYMBOL ANY] ...} ANY} s)
     (let* ([sl (s-exp->list s)]
            [bindings (s-exp->list (second sl))])
       (letI (map (lambda (bnd)
                    (assert-not-reserved
                     (s-exp->symbol (first (s-exp->list bnd)))))
                  bindings)
             (map (lambda (bnd)
                    (parse* (second (s-exp->list bnd)) expand))
                  bindings)
             (parse* (third sl) expand)))]
    [(s-exp-match? `{if0 ANY ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (if0I (parse* (second sl) expand)
             (parse* (third sl) expand)
             (parse* (fourth sl) expand)))]
    [else (error 'parse "invalid input")]))

(module+ test
  (define sample-env (list (tbind 'Equatable (intT 'Equatable))
                           (tbind 'Comparable (intT 'Comparable))))
  (define do-nothing (lambda (s) (none)))
  
  (test (parse* `{let {[x 3] [y 7]}
                   {new Foo x y {* x y}}}
                do-nothing)
        (letI '(x y) (list (numI 3) (numI 7))
              (newI 'Foo (list (idI 'x)
                               (idI 'y)
                               (multI (idI 'x) (idI 'y)))))))

(parse-t-class* : (S-Exp Expander T-Env -> (Symbol * ClassT)))
(def* (parse-t-class* s expand tenv)
  (cond
    [(s-exp-match? `{class SYMBOL <= SYMBOL :: {SYMBOL ...}
                      {ANY ...} ANY ...} s)
     (values
      (s-exp->symbol (second (s-exp->list s)))
      (classT (s-exp->symbol (fourth (s-exp->list s)))
              (map s-exp->symbol
                   (s-exp->list (fourth (rest (rest (s-exp->list s))))))
              (map-with tenv expand parse-t-field*
                        (s-exp->list (fourth (rest (rest (rest (s-exp->list s)))))))
              (map-with tenv expand parse-t-method*
                        (rest (rest (rest (rest (rest (rest (rest (s-exp->list s)))))))))))]
    [else (error 'parse-t-class "invalid input")]))

(parse-t-method* : (S-Exp Expander T-Env -> Method))
(def* (parse-t-method* s expand tenv)
  (cond
    [(s-exp-match? `[SYMBOL {[SYMBOL : ANY]} : ANY ANY] s)
     (let* ([sl (s-exp->list s)]
            [m-name (s-exp->symbol (first sl))]
            [arg-name (identifier! (first (s-exp->list (first (s-exp->list (second sl))))))]
            [arg-t (parse-type* (third (s-exp->list (first (s-exp->list (second sl)))))
                                expand tenv)]
            [result-t (parse-type*  (fourth sl) expand tenv)]
            [body (parse* (fourth (rest sl)) expand)])
       (values m-name (values arg-name (methodT arg-t result-t body))))]
    [else (error 'parse-t-method "invalid input")]))

(parse-t-field* : (S-Exp Expander T-Env -> Field))
(def* (parse-t-field* s expand tenv)
  (cond
    [(s-exp-match? `[SYMBOL : ANY] s)
     (values (identifier! (first (s-exp->list s)))
             (parse-type* (third (s-exp->list s)) expand tenv))]
    [else (error 'parse-t-field (string-append "invalid input: "
                                               (to-string s)))]))

(module+ test
  (test (parse-t-class* `{class Foo {}}
                        (lambda (s)
                          (cond
                            [(s-exp-match? `{class SYMBOL {ANY ...} ANY ...} s)
                             (let ([sl (s-exp->list s)])
                               (some `{class ,(second sl) <= Object :: {}
                                        ,(third sl)
                                        ,@(rest (rest (rest sl)))}))]
                            [else (none)]))
                        empty)
        (pair 'Foo (classT 'Object empty empty empty)))
  (test (parse-type* `num do-nothing empty)
        (numT))
  (test (parse-type* `Object do-nothing empty)
        (objT 'Object))
  (test/exn (parse-type* `{} do-nothing empty)
            "invalid input")
  (test (parse-type* `Bool do-nothing (list (tbind 'Bool (intT 'Bool))))
        (intT 'Bool))
  (test (parse-type* `Bool do-nothing (list (tbind 'Bool (objT 'Bool))))
        (objT 'Bool))

  (test (parse-t-field* `[x : num]  do-nothing empty)
        (values 'x (numT)))
  (test (parse-t-field* `[foo : Comparable]
                        do-nothing
                        (list (tbind 'Comparable (intT 'Comparable))))
        (values 'foo (intT 'Comparable)))
  (test/exn (parse-t-field* `{x 1} do-nothing empty)
            "invalid input")

  (test (parse-t-method* `[m {[arg : num]} : Object this] do-nothing empty)
        (values 'm (values 'arg (methodT (numT) (objT 'Object) (thisI)))))
  (test/exn (parse-t-method* `{m 1} do-nothing empty)
            "invalid input")
  (test (parse-t-method* `[f {[x : Comparable]} : num 4]
                         do-nothing
                         (list (tbind 'Comparable (intT 'Comparable))))
        (values 'f (values 'x (methodT (intT 'Comparable) (numT) (numI 4)))))

  (test (parse-t-class* `{class Posn3D <= Posn :: {}
                           {[x : num] [y : num]}
                           [m1 {[arg : num]} : num arg]
                           [m2 ([_ : num]) : Object this]}
                        do-nothing empty)
        (values 'Posn3D
                (classT 'Posn
                        empty
                        (list (values 'x (numT))
                              (values 'y (numT)))
                        (list (values 'm1 (values 'arg (methodT (numT) (numT) (idI 'arg))))
                              (values 'm2 (values '_ (methodT (numT) (objT 'Object) (thisI))))))))
  (test/exn (parse-t-class* `{class} do-nothing empty)
            "invalid input"))

(parse-sig* : (S-Exp Expander T-Env -> (Symbol * Signature)))
(def* (parse-sig* s expand tenv)
  (cond
    [(s-exp-match? `[SYMBOL : ANY -> ANY] s)
     (pair (s-exp->symbol (first (s-exp->list s)))
           (sig (parse-type* (third (s-exp->list s)) expand tenv)
                (parse-type* (fourth (rest (s-exp->list s))) expand tenv)))]
    [else (error 'parse-sig "invalid input")]))


(module+ test
  (test (parse-sig*  `[f : num -> num] do-nothing empty)
        (pair 'f (sig (numT) (numT))))
  (test (parse-sig*  `[f : Comparable -> num]
                     do-nothing
                     (list (tbind 'Comparable (intT 'Comparable))))
        (pair 'f (sig (intT 'Comparable) (numT))))
  (test/exn (parse-sig*  `[f : Comparable -> num] do-nothing empty)
            "not found")
  (test/exn (parse-sig*  `[f : {} -> {}] do-nothing empty)
            "invalid input")
  (test/exn (parse-sig*  `{f num num} do-nothing empty)
            "invalid input"))

(parse-interface* : (S-Exp Expander T-Env -> (Symbol * Interface)))
(def* (parse-interface* s expand tenv)
  (cond
    [(s-exp-match? `{interface SYMBOL <= {SYMBOL ...}
                      ANY ...} s)
     
     (pair (identifier! (second (s-exp->list s)))
           (interf (map s-exp->symbol
                        (s-exp->list (fourth (s-exp->list s))))
                   (map-with tenv expand parse-sig*
                             (rest (rest (rest (rest (s-exp->list s))))))))]
    [else (error 'parse-interface "invalid input")]))

(parse-type* : (S-Exp Expander T-Env -> Type))
(def* (parse-type* s expand tenv)
  (cond
    [(s-exp-match? `num s)
     (numT)]
    [(s-exp-match? `SYMBOL s)
     (find-type tenv s)]
    [else (error 'parse-type* "invalid input")]))

(module+ test
  (test (parse-interface* `{interface Foo <= {}
                             [f : num -> num]}
                          do-nothing sample-env)
        (pair 'Foo (interf '() (list (pair 'f (sig (numT) (numT)))))))
  
  (test (parse-interface* `{interface Equatable <= {}
                             [=? : Equatable -> num]}
                          do-nothing sample-env)
        (pair 'Equatable
              (interf '() (list (pair '=? (sig (intT 'Equatable) (numT)))))))
  
  (test (parse-interface* `{interface Comparable <= {Equatable}
                             [>? : Equatable -> num]
                             [<? : Equatable -> num]}
                          do-nothing sample-env)
        (pair 'Comparable
              (interf '(Equatable) (list (pair '>? (sig (intT 'Equatable) (numT)))
                                         (pair '<? (sig (intT 'Equatable) (numT)))))))
  (test/exn (parse-interface* `{interface Comparable {}
                                 [>? : Equatable -> num]
                                 [<? : Equatable -> num]}
                              do-nothing sample-env)
            "invalid input")
  (test/exn (parse-interface* `{interface Foo <= {}
                                 [do-foo : {} -> 0]}
                              do-nothing sample-env)
            "invalid input"))