# CAS706_assignment3_oz

I feel very painful to write in oz.. :(
I implement type reconstruct and constraint collection.
I don’t have time to finish all requirements in oz. However I consider other parts are not hard because almost all necessary features (OOP style, records operation, pattern matching etc.) are used in type reconstruct and constraint collection. Rest work should be translation work from above 3 PLs to OZ codes.

/*From untyped term to typed term*/
T1 = {Annotate I1 E1}
/*collect constraints from typed term*/
C1 = {Collect T1}
/*Check constraints set*/
{Browse C1.1.typeA.name}
{Browse C1.1.typeB.name}


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
{Browse {E1 get('z' $)}}*/
