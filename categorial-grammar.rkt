#lang racket
;;; categorial-grammar.rkt
;;; by Daniel J. Rothblatt, 4/5/2016

;;; this project parses a categorial grammar written with the following rule schema:
;;; X/Y Y => X (X/Y read: "X over Y")
;;; Y Y\X => X (Y\X read: "Y under X")
;;; due to complications with backslashes, we will be using '|\| to write "\"

;;; to add: Variable types
;;; Ex: &: (x\x)/x
;;;   A dog & a cat : np
;;;   Dot is cute & Yakko yaks : s
;;;   Possible idea: have a marker 'var indicating this a variable type?
;;;   (Upon instantiation it would be removed)

;;; to add: Printing symbols
;;; on top of that, create a REPL that allows a good interface with user

;;; problem: (parse (list is-even z !)) should => (((is-even z !) (bool)))
;;; currently => (((is-even z) (bool)) ((!) (int \ int)))
;;; in other words, we have a precedence issue
;;; how can we establish precedence?
;;; possibility: in addition to typing, associate a precedence with each label
;;;   BUT: How do we assign precedences to compound phrases?
;;;   BUT: What do we do if there's a precedence tie?

;;; problem: for any objects x, y of atomic type t, (parse (list x y)) => (((x y) ()))
;;; should => (((x) t) ((y) t))
;;; SOLVED: problem was assuming an atomic type has a source/target. It does not.

;; constructors for syntactic categories
(define make-category
  (λ (w type)
    `((,w) ,type)))
(define make-variable-category
  (λ (w type)
    `((,w) ,type 'var)))

(define-syntax define-category
  (syntax-rules (with var const)
    [(_ cat with type const)
     (define cat
       (λ (w)
         (make-category w type)))]
    [(_ cat with type var)
     (define cat
       (λ (w)
         (make-variable-category w type)))]))

(define-category noun with '(n) const)
(define-category noun-phrase with '(np) const)
(define-category det with '(np / n) const)
(define-category adj with '(n / n) const)
;; INTERESTING QUESTION: What to do with ambitransitive verbs?
;; EX: eat, drink, scheme
;; You could label them: eat-t, eat-i -- and then remove the labels during parsing?
;; But you want the system to determine what is appropriate...
(define-category verb-intrans with '(np |\| s) const)
(define-category verb-trans with '((np |\| s) / np) const)
(define-category preposition with '((s |\| s) / np) const)
(define-category s-conjunction with '((s |\| s) / s) const)
(define-category np-conjunction with '((np |\| np) / np) const)
(define-category conjunction with '((x |\| x) / x) var)

(define-syntax define-word
  (syntax-rules ()
    [(_ word type)
     (define word (type 'word))]))

(define-syntax define-words
  (syntax-rules ()
    [(_ type w) (define-word w type)]
    [(_ type w1 w2 ...)
     (begin (define-word w1 type)
            (define-words type w2 ...))]))

;; words for a toy categorial grammar
(define-words noun
  dog cat scheme taco bean paddle man woman goat pig corpse worm schemer outhouse)
(define-words noun-phrase
  daniel oliver dennis yakko wakko dot everyone no-one someone everybody nobody somebody)
(define-words det
  the a an some all this that these those my your his her its our their)
(define-words adj
  red small big shiny clever clear young old)
(define-words verb-intrans
  drowned flew screamed walked jumped died schemed)
(define-words verb-trans
  chased hated loved killed)
(define-words preposition
  in out on off about around with over under)

;(define-word & s-conjunction)
;(define-word \| s-conjunction)
;(define-word andn np-conjunction)
;(define-word & conjunction)

;; example noun phrases
(define np1 (list the cat))
(define np2 (list a clever scheme))
(define np3 (list the big red dog))

;; example sentences
(define s1 (list oliver drowned))
(define s2 (list the big cat drowned))
(define s3 (list the big red dog chased a cat))
;(define s4 (list the clever cat drowned & a big shiny red dog chased oliver))

;; ungrammatical phrases
(define bad1 (list a cat chased)) 
(define bad2 (list oliver shiny))

;; sample types for a static typing system
(define-category int with '(int) const)
(define-category bool with '(bool) const)
(define-category bool-over-int with '(bool / int) const)
(define-category bool-under-int with '(int |\| bool) const)
(define-category int-over-int with '(int / int) const)
(define-category int-under-int with '(int |\| int) const)

(define-word t bool)
(define-word z int)
(define-word s int-over-int)
(define-word ! int-under-int)
(define-word is-even bool-over-int)

;; representation of a syntactic object:
;; obj = (list labels type)
;; where: 
;;   labels a list of symbols, and
;;   type a list of symbols (potentially nested)

(define labels-of
  (λ (obj)
    (car obj)))

(define type-of
  (λ (obj)
    (cadr obj)))

;; because a type is a list, we check if it's a singleton list to determine whether it is atomic
(define atomic-type?
  (λ (type)
    (null? (cdr type))))

;; determines which piece of the (composite) type is input and which output
;; #t <= type = X / Y 
;; #f <= type = X \ Y
;; a composite type is always length 3, and second element always either / or \
(define over?
  (λ (type)
    (eq? '/ (cadr type)))) 

;; function application in Combinatory Categorial Grammar (CCG)
(define handle-application
  (λ (t1 t2 end-label)
    (let ((wrap (λ (tar) ((if (list? tar) identity list) tar))))
      (match (list t1 t2)
        [(list (list tar '/ src) (list src)) ; y/x x => y
         (list end-label (wrap tar))]
        [(list (list src) (list src '|\| tar)) ; x x\y => y
         (list end-label (wrap tar))]
        [_ #f]))))
  
;; combinator B in CCG
(define handle-composition
  (λ (t1 t2 end-label)
    (match (list t1 t2)
      [(list (list x '/ y) (list y '/ z)) ; x/y y/z => x/z
       (list end-label (list x '/ z))]
      [(list (list z '|\| y) (list y '|\| x)) ; z\y y\x => z\x
       (list end-label (list z '|\| x))]
      [_ #f])))

;; works because our current system has variables marked with an additional 'var
(define variable?
  (λ (obj)
    (= 3 (length obj))))

;; Assumes only one var (seems like a fair assumption on linguistic grounds until proven inadequate)
(define instantiate-var
  (λ (type replacement)
    (map (λ (x) (if (pair? x)
                    (instantiate-var x replacement) ; because types can contain types
                    (if (nor (eq? x '/) ; keep the overs and unders as they are, change everything else
                                 (eq? x '|\|))
                        (if (atomic-type? replacement) (car replacement) replacement)
                        x)))
         type)))

;; if one obj is a var, tests if type can be instantiated using type of the other
;; this will work because I assume variable types are composite
;; a better system will be necessary for CS purposes, but probably not linguistic purposes
(define assimilate-variables
  (λ (obj1 obj2)
    (let ([type1 (type-of obj1)]
          [type2 (type-of obj2)])
      (cond
        [(variable? obj1)
         (if (and (not (variable? obj2))
                  (over? type1))
             (list (labels-of obj1) (instantiate-var type1 type2))
             #f)]
        [(variable? obj2)
         (if (and (not (variable? obj1))
                  (not (over? type2)))
             (list (labels-of obj2) (instantiate-var type2 type1))
             #f)]
        [else #f]))))

;; merges two syntactic objects when possible
;; currently handles application and composition
(define resolve-objects
  (λ (obj1 obj2)
    ;; get some useful properties of the objects...
    (let ([type1 (type-of obj1)]
          [type2 (type-of obj2)]
          [end-label (append (labels-of obj1) (labels-of obj2))]) 
        ;; ...and merge the objects!
        (let ([applied (handle-application type1 type2 end-label)])
          (if applied applied
              (let ([composed (handle-composition type1 type2 end-label)])
                (if composed composed
                    #f)))))))

;; performs one scan of the parser
(define one-pass-left-to-right
  (λ (exp)
    (cond
      [(null? exp) null]
      [(null? (cdr exp)) exp]
      [else
       (let* ([fst (car exp)]
              [snd (cadr exp)]
              [resolved (resolve-objects fst snd)])
         (if resolved
             (cons resolved (one-pass-left-to-right (cddr exp))) ; because resolved takes care of two objects, we skip *two* spaces ahead
             (cons fst (one-pass-left-to-right (cdr exp)))))]))) ; otherwise, we cdr down exp normally

;; parses as much as possible
;; There is no guarantee that exp will be fully parsed -- length of output may vary
(define parse-from-left-to-right
  (λ (exp)
    (let ([parsed (one-pass-left-to-right exp)])
      (if (equal? parsed exp) ; => exp is a fixed point of parser (so it's fully parsed)!
          parsed
          (parse-from-left-to-right parsed)))))

;; EX: (parse-1 (list a dog chased my cat))
(define parse-1 parse-from-left-to-right)

;; EX: (parse-2 a dog chased my cat)
(define parse-2
  (lambda exp
    (parse-1 exp)))
