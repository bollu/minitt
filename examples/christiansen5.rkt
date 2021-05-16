(zero-t 0)
(add-one-t add1)
(three 
  (∈ nat ($ add1 ($ add1 ($ add1 0))))) 
(threeNoType ($ add1 ($ add1 ($ add1 0)))) 

(add (∈ (→ nat (→ nat nat))
        (λ n (λ k (rec nat n 
                       k
                       (λ pred (λ s ($ add1 s))))))))

(add1-zero ($ add1 0))
(zero+_ ($ add 0))

(sixNoType ($ ($ add three) three))

(six (∈ nat
        ($ ($ add three) three)))
