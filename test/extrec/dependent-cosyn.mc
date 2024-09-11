lang L0
  cosyn FooType = {a : Int} 

  cosyn BarType = {a : Int, foos : [extrec {FooType of m}]} 

  -- sem sum : all m. extrec {BarType of m} -> Int
  sem sum : < L0::BarType -> Int
  sem sum =
  | b -> 
    let foos = b.foos in 
    let as = map (lam f : extrec {FooType of Unknown}. f.a) foos in 
    addi (foldl addi 0 as) b.a
end

mexpr
use L0 in 
let f1 = {FooType of a = 10} in 
let f2 = {FooType of a = 20} in 
let f3 = {FooType of a = 30} in 
let b = {BarType of a = 20, foos = [f1, f2, f3]} in 
utest sum b with 80 using eqi in
-- utest sum f2 with 30 using eqi in

()


