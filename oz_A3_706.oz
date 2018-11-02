declare

class Term from BaseObject
   feat term
   meth init skip end 
end

class INT from Term
   feat
      value
      int
   meth init skip end 
   /*meth init(v)
      value = v
   end*/
end

class BOOL from Term
   feat
      value
      bool
   meth init skip end 
end

class VAR from Term
   feat
      char
      var
   meth init skip end 
end

class FUN from Term
   feat
      function
      param
      body
   meth init skip end 
end

class APP from Term
   feat
      application
      func
      arg
   meth init skip end 
end

class CALC from Term
   feat
      calc
      op
      arg1
      arg2
   meth init skip end 
end

class TypedTerm from BaseObject
   feat
      typedTerm
      name
      ty
   meth init skip end 
end

class T_INT from TypedTerm
   feat
      value
      tInt
   meth init skip end 
   /*meth init(v)
      value = v
   end*/
end

class T_BOOL from TypedTerm
   feat
      value
      tBool
   meth init skip end 
end

class T_VAR from TypedTerm
   feat
      char
      tVar
   meth init skip end 
end

class T_FUN from TypedTerm
   feat
      tFun
      param
      body
   meth init skip end 
end

class T_APP from TypedTerm
   feat
      tApp
      function
      arg
   meth init skip end 
end

class T_CALC from TypedTerm
   feat
      tCalc
      op
      arg1
      arg2
   meth init skip end 
end

class Type from BaseObject
   feat
      type
      name
   meth init skip end 
end

class TyInt from Type
   feat tyInt
end

class TyBool from Type
   feat tyBool 
end

class TyFun from Type
   feat
      tyFun
      paramTy
      returnTy
end

class TyVar from Type
   feat
      tyVar
      num
end

class TypeEnv from BaseObject
   attr
      Env
      Num
      NewVar
   meth init()
      Env := e(1)
      Num := 0
   end
   meth get(K $)
      @Env.K
   end
   meth set(K V)
      /*Env := {AdjoinAt Env K V }*/
      Env := {AdjoinAt @Env K V}
   end
   meth freshVar($)
      Num := @Num + 1
      NewVar := {New TyVar init}
      @NewVar.num = @Num
      @NewVar     
   end
end

class Constraint from BaseObject
   feat
      typeA
      typeB
   meth init skip end 
end

fun {Collect Term}
   if {Value.hasFeature Term tInt}
   then
      local Con Ty in
	 Con = {New Constraint init}
	 Con.typeA = Term.ty
	 Ty = {New TyInt init}
	 Ty.name = 'TyInt'
	 Con.typeB = Ty
	 c(Con)
      end
   elseif {Value.hasFeature Term tBool}
   then
      local Con Ty in
	 Con = {New Constraint init}
	 Con.typeA = Term.ty
	 Ty = {New TyBool init}
	 Ty.name = 'TyBool'
	 Con.typeB = Ty
	 c(Con)
      end
   elseif {Value.hasFeature Term tFun}
   then
      local Con Ty in
	 Con = {New Constraint init}
	 Con.typeA = Term.ty
	 Ty = {New TyFun init}
	 Ty.name = 'TyFun'
	 Ty.paramTy = Term.param.ty
	 Ty.returnTy = Term.body.ty
	 Con.typeB = Ty
	 cSet = {Collect Term.body}
	 {Tuple.append cSet c(Con)}
	 /*cSet*/
      end
   elseif {Value.hasFeature Term tApp}
   then
      local Con Ty in
	 Con = {New Constraint init}
	 Con.typeA = Term.function.ty
	 Ty = {New TyFun init}
	 Ty.name = 'TyFun'
	 Ty.paramTy = Term.arg.ty
	 Ty.returnTy = Term.ty
	 Con.typeB = Ty
	 cSet1 = {Collect Term.function}
	 cSet2 = {Collect Term.arg}
	 {Tuple.append {Tuple.append cSet1 c(Con)} cSet2}
      end
   elseif {Value.hasFeature Term tVar}
   then
      c()
   elseif {Value.hasFeature Term tCalc}
   then
      local Con1 Con2 Con3 in
	 Con1 = {New Constraint init}
	 Con1.typeA = Term.ty
	 Con1.typeB = Term.arg1.ty
	 Con2 = {New Constraint init}
	 Con2.typeA = Term.ty
	 Con2.typeB = Term.arg2.ty
	 Con3 = {New Constraint init}
	 Con3.typeA = Term.ty
	 Con3.typeB = {New TyInt init}
	 cSet1 = {Collect Term.arg1}
	 cSet2 = {Collect Term.arg2}
	 {Tuple.append {Tuple.append cSet1 c(Con1 Con2 Con3)} cSet2}
      end
   end
end

declare T_Term Ty T_Term2 Ty2 T
fun {Annotate Term Env}
   if {Value.hasFeature Term int}
   then
      local T_Term Ty in
	 T_Term = {New T_INT init}
	 T_Term.value = Term.value
	 T_Term.name = 'T_INT'
	 Ty = {Env freshVar($)}
	 Ty.name = 'TyVar'
	 T_Term.ty = Ty
	 T_Term
      end
   elseif {Value.hasFeature Term bool}
   then
      local T_Term Ty in
	 T_Term = {New T_BOOL init}
	 T_Term.value = Term.value
	 T_Term.name = 'T_BOOL'
	 Ty = {Env freshVar($)}
	 Ty.name = 'TyVar'
	 T_Term.ty = Ty
	 T_Term
      end
   elseif {Value.hasFeature Term function}
   then
      local T_Term T_Term2 Ty Ty2 in
	 T_Term = {New T_FUN init}
	 Ty2 = {Env freshVar($)}
	 {Env set(Term.param Ty2)}
	 T_Term.name = 'T_FUN'
	 T_Term2 = {New T_VAR init}
	 T_Term2.char = Term.param
	 T_Term2.ty = Ty2
	 Ty = {Env freshVar($)}
	 T_Term.param = T_Term2
	 T_Term.ty = Ty
	 /*T = Term.body
	 T = {Annotate Term.body Env}*/
	 T_Term.body = {Annotate Term.body Env}
	 /*T_Term.body = {New T_VAR init}*/
	 T_Term
      end
   elseif {Value.hasFeature Term var}
   then
      local T_Term Ty in
	 Ty = {Env get(Term.char $)}
	 T_Term = {New T_VAR init}
	 T_Term.name = 'T_VAR'
	 T_Term.ty = Ty
	 T_Term.char = Term.char
	 T_Term
      end
   elseif {Value.hasFeature Term app}
   then
      local T_Term Ty in
	 T_Term = {New T_APP init}
	 Ty = {Env freshVar($)}
	 Ty.name = 'TyVar'
	 T_Term.ty = Ty
	 T_Term.name = 'T_APP'
	 T_Term.function = {Annotate Term.function Env}
	 T_Term.arg = {Annotate Term.arg Env}
	 T_Term
      end
   elseif {Value.hasFeature Term calc}
   then
      local T_Term Ty in
	 T_Term = {New T_CALC init}
	 Ty = {Env freshVar($)}
	 Ty.name = 'TyVar'
	 T_Term.ty = Ty
	 T_Term.name = 'T_CALC'
	 T_Term.op = Term.op
	 T_Term.arg1 = {Annotate Term.arg1 Env}
	 T_Term.arg2 = {Annotate Term.arg2 Env}
	 T_Term
      end
   end  
end

declare I1 I2 V1 C1 F1 A1
I1 = {New INT init}
I1.value = 1
/*{Browse I1.value}*/

I2 = {New INT init}
I2.value = 2
/*{Browse I2.value}*/

V1 = {New VAR init}
V1.char = 'x'
/*{Browse V1.name}*/

C1 = {New CALC init}
C1.op = '+'
C1.arg1 = V1
C1.arg2 = I1
/*{Browse C1.arg1.name}*/

F1 = {New FUN init}
F1.param = 'x'
F1.body = V1

A1 = {New APP init}
A1.func = F1
A1.arg = I2

declare E1 NV1
E1 = {New TypeEnv init}
/*{E1 set('z' 3)}
{Browse {E1 get('z' $)}}
NV1 = {E1 freshVar($)}
{Browse NV1.num}*/

declare T1 T2 C1 T_Term T_Term2 Ty Ty2
T1 = {Annotate I1 E1}
C1 = {Collect T1}
/*{Browse T1.value}
{Browse T1.name}
{Browse T1.ty.name}
{Browse T1.ty.num}
T2 = {Annotate F1 E1}
{Browse T2.name}*/
/*{Browse T2.ty.name}
{Browse T2.ty.num}*/
/*T_Term = {New T_FUN init}
Ty2 = {E1 freshVar($)}
{E1 set(F1.param Ty2)}
T_Term.name = 'T_FUN'
T_Term2 = {New T_VAR init}
T_Term2.char = F1.param
T_Term2.ty = Ty2
Ty = {E1 freshVar($)}
T_Term.param = T_Term2
T_Term.ty = Ty
{Browse T_Term.name}
T1 = {E1 get(F1.body.char $)}
{Browse T1.num}*/