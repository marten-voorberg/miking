lang CosemExample 
  cosyn MyEnv = {x : Int,
                 y : Int,
                 z : Int,
                 s : String}

  cosem defaultEnv param param2 = 
  | {MyEnv of x, y} <-
    {x = subi 100 param, y = param}
  | {MyEnv of z} <-
    {z = param2}
  | {MyEnv of s} <-
    {s = "abcd"}
end

lang SomeExtensionLang = CosemExample
  cosyn MyEnv *= {abcd : String}

  cosem defaultEnv param param2 *= 
  | {MyEnv of abcd} <-
    {abcd = "something else"}
end

mexpr 
use SomeExtensionLang in 
let env = defaultEnv 10 20 in 
utest env.x with 90 using eqi in 
utest env.y with 10 using eqi in 
utest env.z with 20 using eqi in 
()