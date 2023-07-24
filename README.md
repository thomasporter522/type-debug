## Type Debug System

Currently the only file is a jumble of functions, sorry.

I speculate that the current system accepts all typeable, closed programs with all variable names distict, and infers essentially all possible information about the types of the variables and subexpressions. WARNING: it will fail gracelessly for many untypable inputs, and will not terminate given some inputs. 

Two main directions to go for the prototype; handle bad inputs better, and return compositional explanations of typing decisions or obstacles. Both require annotating the expressions and contexts. 