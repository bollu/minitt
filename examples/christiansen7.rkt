(zero-t (∈ nat 0))
(three 
  (∈ nat (+1 (+1 (+1 0))))) 

(add (∈ (→ nat (→ nat nat))
        (λ n (λ k (ind-nat n
                       (λ nat-mot nat)
                       k
                       (λ pred (λ s (+1 s))))))))

(add1-zero (∈ nat (+1 0)))
(zero+_ ($ add 0))


(six (∈ nat
        ($ ($ add three) three)))

(id (∈ [→ nat nat] (λ x x)))
(ap-id-behind-lam (∈ [→ nat nat] (λ x ($ id x))))