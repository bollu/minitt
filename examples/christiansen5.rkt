(zero-t 0)
(three 
  (∈ nat (+1 (+1 (+1 0))))) 
(threeNoType (+1 (+1 (+1 0)))) 

(add (∈ (→ nat (→ nat nat))
        (λ n (λ k (rec nat n 
                       k
                       (λ pred (λ s (+1 s))))))))

(add1-zero (+1 0))
(zero+_ ($ add 0))

(sixNoType ($ ($ add three) three))

(six (∈ nat
        ($ ($ add three) three)))

(id (∈ [→ nat nat] (λ x x)))
(ap-id-behind-lam (∈ [→ nat nat] (λ x ($ id x))))
