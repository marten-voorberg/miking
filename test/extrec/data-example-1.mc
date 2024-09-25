mexpr
rectype Foo in 
recfield x : all m. Foo -> Int in 
recfield y : all m. Foo -> Int in 
recfield z : all m. Foo -> Int in 

let addXY : all m :: {Foo [> x y]}.
          extrec {Foo of m} -> Int = 
  lam r. addi r.x r.y in

let rXYZ = {Foo of x = 1, y = 2, z = 3} in 
utest addXY rXYZ with 3 in 

let rXY = {Foo of x = 20, y = 3} in 
utest addXY rXY with 23 in

()
