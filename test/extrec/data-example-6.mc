mexpr
rectype Foo in 
recfield x : all m. Foo -> Int in 
recfield y : all m. Foo -> Int in 

rectype Bar in 
recfield f1 : all m. Bar -> extrec {Foo of m} in 
recfield f2 : all m. Bar -> extrec {Foo of m} in 

let setX : all m :: {Bar [< f1 f2], Foo [< x]}. 
            Int -> Int -> extrec {Bar of m}
  = lam x1. lam x2. 
    {Bar of f1 = {Foo of x = x1}, f2 = {Foo of x = x2, y = 2}}
in 

let r = setX 10 20 in 

let f1 = r.f1 in 
utest f1.x with 10 in 

let f2 = r.f2 in 
utest f2.x with 20 in 

()
