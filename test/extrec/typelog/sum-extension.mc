include "../sum-extension.mc"

mexpr
let x = 
  use ArithLang in 
  print "ArithLang::eval : ";
  print (typeof eval);
  print "\n" in 

let x = 
  use ConditionalLang in 
  print "ConditionalLang::eval : ";
  print (typeof eval);
  print "\n" in 

()