include "../sum-contraction-inferred-types.mc"

mexpr
use SugarArith in 
print "eval : ";
print (typeof eval);
print "\n\n";

print "expr3 : ";
let expr = TmInt {TmIntType of val = 42} in
let expr3 = TmIncr {TmIncrType of e = expr} in 
print (typeof expr3);
print "\n\n";


print "desugar : ";
print (typeof desugar);
print "\n\n";

()