;; ---------------------------
;; Gavin Gray
;; L3 bindings for Chez Scheme
;; An attempt, except I can't rebind ' for characters.
;; 30.03.2022

(define-syntax def
  (syntax-rules ()
    [(_ x ...) (define x ...)]))

(define-syntax defrec
  (syntax-rules ()
    [(_ x ...) (define x ...)]))

(define-syntax fun
  (lambda (x)
    (syntax-case x ()
      [(_ (n ...) b ...)
       #'(lambda (n ...) b ...)])))

(define-syntax let*
  (lambda (x)
    (syntax-case x ()
      [(_ () b ...)
       #'(let () b ...)]
      [(_ (l r ...) b ...)
       #'(let (l)
           (let* (r ...)
             b ...))])))

((fun (x) x) 10)
