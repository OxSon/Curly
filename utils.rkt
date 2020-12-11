#lang plait

;; Various helper functions that don't require knowledge of any
;; of other modules

; and one trivial macro :)
(define-syntax-rule (rethrow call sym msg)
  (try call (lambda () (error sym msg))))

(define (find [l : (Listof (Symbol * 'a))] [name : Symbol]) : 'a
  (type-case (Listof (Symbol * 'a)) l
    [empty
     (error 'find (string-append "not found: " (symbol->string name)))]
    [(cons p rst-l)
     (if (symbol=? (fst p) name)
         (snd p)
         (find rst-l name))]))

(module+ test
  (print-only-errors #t)
  (test (find (list (values 'a 1)) 'a)
        1)
  (test (find (list (values 'a 1) (values 'b 2)) 'b)
        2)
  (test/exn (find empty 'a)
            "not found: a")
  (test/exn (find (list (values 'a 1)) 'x)
            "not found: x"))

(define (assert-eq-len! [as : (Listof 'a)]
                        [bs : (Listof 'b)]
                        [caller-name : Symbol])
  (let ([len-a (length as)]
        [len-b (length bs)])
    (if (= len-a len-b)
        (void)
        (error caller-name (string-append "all lists must have same size: "
                                          (string-append (to-string len-a)
                                                         (string-append " vs "
                                                                        (to-string len-b))))))))

(define (fold_2 step acc as bs left?)
  (let ([target (if left?
                    (pair 'foldl2 foldl2*)
                    (pair 'foldr2 foldr2*))])
    (begin (assert-eq-len! as bs (fst target))
           ((snd target) step acc as bs))))

(define foldl2
  (lambda (step acc as bs)
    (fold_2 step acc as bs #t)))

(define foldr2
  (lambda (step acc as bs)
    (fold_2 step acc as bs #f)))

(define foldl2* : (('a 'b 'acc -> 'acc) 'acc (Listof 'a) (Listof 'b) -> 'acc)
  (lambda (step acc as bs)
    (if (empty? as)
        acc
        (foldl2* step
                 (step (first as)
                       (first bs)
                       acc)
                 (rest as)
                 (rest bs)))))

(define foldr2* : (('a 'b 'acc -> 'acc) 'acc (Listof 'a) (Listof 'b) -> 'acc)
  (lambda (step acc as bs)
    (if (empty? as)
        acc
        (step (first as)
              (first bs)
              (foldr2* step acc (rest as) (rest bs))))))

;; same as foldl2 but it stops folding when the first list is empty,
;; and tolerates len-a <= len-b rather than only len-a = len-b.
;; We use it for when classes static send to their super classes
;; which might have fewer fields than the subclass
(define (foldl2-until step acc as bs)
  (if (<= (length as) (length bs))
      (foldl2-until* step acc as bs)
      (error 'foldl2-until "first list length must be <= second list lsength")))
(define (foldl2-until* step acc as bs)
  (if (empty? as)
      acc
      (foldl2-until* step
                     (step (first as)
                           (first bs)
                           acc)
                     (rest as)
                     (rest bs))))

(module+ test
  (test/exn (foldl2-until (lambda (x y z) x)
                          'z
                          '(a b c)
                          '(c d))
            "first list length must be <=")
  (test (foldl2-until
         (lambda (x y z) (+ x (+ y z)))
         0
         '(1 2 3)
         '(4 5 6 7 8 9 10))
        21))

(module+ test
  (define f (lambda (a b c) c))
  (test (f 1 2 3) 3)

  (test/exn (foldl2 f 0 '(1 2 3) '(1 2))
            "all lists must have same size: 3 vs 2")
  (test/exn (foldl2 f 0 '() '(1))
            "all lists must have same size: 0 vs 1")
  (test (foldl2 (lambda (a b acc) (* acc (+ a b)))
                1
                '(1 2 3)
                '(1 2 3))
        (* 8 6))
  (test (foldr2 (lambda (a b acc)
                  (string-append acc
                                 (string-append a
                                                b)))
                "beginning "
                '("foo bar baz")
                '("fee bee bez"))
        "beginning foo bar bazfee bee bez")
  (test/exn (foldr2 f 0 '() '(1 2 3))
            "all lists must have same size"))

; short circuiting predicate OR fold
; NOTE: `p` should not mutate its argument
(define (any? [items : (Listof 'a)] [p : ('a -> Boolean)]) : Boolean
  (let/cc k
    (foldl (lambda (item acc)
             (let ([next (p item)])
               (if next
                   ; short circuit
                   (k #t)
                   acc)))
           #f
           items)))

; short circuiting predicate AND fold
; NOTE: `p` should not mutate its argument
(define (all? [items : (Listof 'a)] [p : ('a -> Boolean)]) : Boolean
  (let/cc k
    (foldl (lambda (item acc)
             (let ([next (p item)])
               (if next
                   acc
                   ; short circuit
                   (k #f))))
           #t
           items)))

(module+ test
  (test (any? '(1 3 5 9) even?)
        #f)
  (test (any? '(1 3 2 8 9) even?)
        #t)
  (test (any? (list "foo" "bar" "baz" "buzzzzzzzzz")
              (lambda (s)
                (> 5 (string-length s))))
        #t)
  (test (all? (build-list 9000 (lambda (n) (none)))
              (lambda (s) #f))
        #f)
  (test (all? '(1 3 5 9 11 13) odd?)
        #t)
  
  ;; tests demonstrating short circuiting
  (test (let ([l (list (box (some 1)) (box (some 2)) (box (some 3)))]
              ;; an even? predicate that also mutates
              [p (lambda (b)
                   (let ([v (some-v (unbox b))])
                     (begin
                       (if (even? v)
                           #t
                           (begin
                             (set-box! b (none))
                             #f)))))])
          (begin 
            (any? l p)
            l))
        (list (box (none)) (box (some 2)) (box (some 3))))
        
  (test (let ([l (list (box (some 2)) (box (some 4)) (box (some 1)) (box (some 6)))]
              [p (lambda (b)
                   (type-case (Optionof Number) (unbox b)
                     [(none) #f]
                     [(some n) (begin
                                 (set-box! b (none))
                                 (even? n))]))])
          (begin (all? (list (box (none))) p) ; just for coverage
                 (all? l p)
                 l))
        (list (box (none)) (box (none)) (box (none)) (box (some 6)))))

(define (intersect [a : (Listof 'a)] [b : (Listof 'a)]) : (Listof 'a)
  (foldr (lambda (next acc)
           (if (member next b)
               (cons next acc)
               acc))
         '()
         a))

(module+ test
  (test (intersect '(k j h b obj) '(l k j h b obj))
        '(k j h b obj))
  (test (intersect '(k j h b obj) '(g b obj))
        '(b obj))
  (test (intersect '(e a obj) '(m k j h b obj))
        '(obj))
  (test (intersect '(i h b obj) '(g b obj))
        '(b obj)))

(define (intersect-point [a : (Listof 'a)] [b : (Listof 'a)]) : (Optionof 'a)
  (let/cc k
    (foldl (lambda (next acc)
             (if (member next b)
                 (k (some next))
                 acc))
           (none)
           a)))

(module+ test
  (test (intersect-point '(k j h b obj) '(l k j h b obj))
        (some 'k))
  (test (intersect-point '(k j h b obj) '(g b obj))
        (some 'b))
  (test (intersect-point '(e a obj) '(m k j h b obj))
        (some 'obj))
  (test (intersect-point '(i h b obj) '(g b obj))
        (some 'b)))

;; reserved keywords may not be used as identifiers in any context.
;; Do to the structured nature of our concrete syntax, `let and `where
;; dont' actually need to be on this list, but programs that
;; use them as identifiers can be quite confusing, so we will forbid.
(define reserved-keywords '(this let where))

;; error out if `s is a reserved keyword, otherwise
;; return same value
(define (assert-not-reserved [s : Symbol]) : Symbol
  (if (member s reserved-keywords)
      (error 'parse (string-append
                     "disallowed: "
                     (string-append
                      ;; we use to-string instead of
                      ;; `symbol->string` intentionally
                      ;; (to preserve the leading quote)
                      ;; in order to distinguish the
                      ;; offending name in the error msg
                      (to-string s)
                      " is a reserved keyword")))
      s))
(define identifier! : (S-Exp -> Symbol)
  (lambda (s)
    (assert-not-reserved
     (s-exp->symbol s))))

(module+ test
  (test (member 'this reserved-keywords)
        #t)
  (test/exn (identifier! `let)
            "disallowed")
  (test/exn (identifier! `where)
            "disallowed")
  (test (member 'xKFvvaa93i3fj-2jfDDDD reserved-keywords)
        #f)
  (test (assert-not-reserved 'foo)
        'foo)
  (test/exn (assert-not-reserved 'this)
            "disallowed")
  (test/exn (identifier! `this)
            "disallowed")
  (test (identifier! `foo)
        'foo))