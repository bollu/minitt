(ind nat : []
  ((zero [] : [])
   (succ [(k nat)] : [])))

(ind vec : [(x (ind nat : [])) ]
  ((vzero [] : [(ctor zero [])])
   (vsucc [(v (ind vec : [n]))] : [(ctor succ [n])])))

