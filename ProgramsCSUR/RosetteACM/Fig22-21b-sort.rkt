; Sorting.
; Author: Richard St-Denis, Universite de Sherbrooke, 2022.
#lang rosette
(require "Theories/Fig21b-sorting.rkt")
(current-bitwidth #f)
; Create a distinct symbolic constant of type integer
(define (new-symbolic-index)
  (define-symbolic* s integer?) s )
; Initialize a vector with symbolic constants
(define (initialize-symbolic-vector v)
  (for/list ([i (vector-length v)])
    (vector-set! v i (new-symbolic-index)) ) )
; Solve the sorting problem
(define (run_sort a p n) (solve (assert (apply && (sorted a p (- n 2))))))
; Display the permutation and the sorted array from a solution
(define (display-solution p a s)
  (for ([i (vector-length a)])
    (printf "i~a: ~a\n" i (evaluate (vector-ref p i) s)) )
  (printf "The sorted array:")
  (for ([i (vector-length a)])
    (printf " ~a" (evaluate (vector-ref a (vector-ref p i)) s)) )
  (printf "\n") )
; Instance of the sorting problem
(let* ([A (vector-immutable 6 -3 6 0 6 4 8 7 -3)]
;(let* ([A (vector-immutable 6 -3 6 0 6 4 8 7 -3 -5 2 -2 1 5 -1 0 13 17 -9 9 8 -3 6 -3 6 0 6 4 8 7 -3 -5 2 -2 -4)]
       [n (vector-length A)] [SortA (make-vector n)] )
  (initialize-symbolic-vector SortA)
  (assert (apply && (permutation-a1 SortA n (- n 1))))
  (assert (apply && (permutation-a2 SortA (- n 1) 0)))

  (define t0 (current-seconds))
  (let ([solution (run_sort A SortA n)])
    (if [sat? solution]
        (display-solution SortA A solution)
        (printf "The theory is inconsistent.~n") ) )
  (print (- (current-seconds) t0)) )