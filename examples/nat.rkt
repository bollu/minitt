(letrec Nat U
  (Sum [zero 1] [succ Nat]))
(letrec natrec (Π [C (→ Nat U)] 
                  (→ {$ C zero} 
                     (→ (Π [n Nat] (→ {$ C n} {$ C {$ succ n}})) 
                        (Π [m Nat] {$ C n}))))
  (λ C (λ elimz (λ elimsucc 
                    (fun [elimzero z] 
                         [succ (λ i 
                                  [$ ($ elimsucc i) ($ ($ ($ natrec C) a) elimsucc)])])))))
                     
