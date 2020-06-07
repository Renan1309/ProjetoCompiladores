module KOTLIN-SYNTAX 
    import DOMAINS
    syntax Pgm ::= "fun main()" "{" Block "}"      

    syntax Skip ::= "Skip"

    syntax Block ::= "{" Stmt "}" 
                | Stmt

    syntax Stmt ::= "if" "(" BExp ")" Block [strict(1)]
                | "if" "(" BExp ")" Block ElseIfStmt [strict(1)]
                | BExp "?" Block ":" Block [strict(1)]
                | "while" "(" BExp ")" Block
                | "do" Block "while" "(" BExp ")"
                | For
                | AExp
                | DecVar ";"
                | Assigner
                | AExpMod 
                | Skip
                | Stmt Stmt [left]

    syntax ListValues ::= List{Int, ","}
    syntax ArrayList ::= "[" ListValues "]"
    
    syntax For ::= "for" "(" Id "in" ArrayList ")" Block

    syntax Type ::= "var" | "val"

    syntax Ids ::= List{Id, ","}

    syntax DecVar ::= Type Ids

    syntax UniqueIdAssigner ::= Id "=" AExp  [strict(2)]

    syntax Assigner ::= DecVar "=" AExp ";" [strict(2)]
                    | UniqueIdAssigner

    syntax ElseIfStmt ::= "else if" "(" BExp ")" Block
                        | "else" Block
                        | "else if" "(" BExp ")" Block ElseIfStmt

    syntax BExp ::= Bool
                    | AExp "<" AExp [strict]
                    | AExp "<=" AExp [strict]
                    | AExp ">" AExp [strict]
                    | AExp ">=" AExp [strict]
                    | AExp "==" AExp 
                    | AExp "&&" AExp 
                    | AExp "||" AExp 
                    | "(" BExp ")" [bracket]

    syntax AExpMod  ::= Id "++" 

    syntax AExp ::= Int | String 
                | Id
                | AExp "+" AExp [seqstrict, left]
                | AExp "-" AExp [seqstrict, left]
                | AExp "*" AExp [seqstrict, left]
                | AExp "/" AExp [seqstrict, left]

    rule fun main() { B:Block } => B [structural]

    rule S1:Stmt S2:Stmt => S1 ~> S2
    
    rule Skip => .
    
    rule if (true) { S:Stmt } => S
    rule if ( B:BExp ) { S:Stmt } => S
    rule if (false) { _ } => Skip
    rule if (true) { B } S:ElseIfStmt => B
    rule if (false) { _ } S:ElseIfStmt => S
    rule else if ( B:BExp ) { S1:Stmt } S2:ElseIfStmt => if ( B ) { S1 } S2
    rule else if ( B:BExp ) { S:Stmt } => if ( B ) { S }
    rule else { S } => S

    rule true ? B:Block : _ => B 
    rule false ? _ : B:Block => B

    rule while (B:BExp) { S:Stmt } => if(B){ S while (B) { S } } [structural]

    rule do { S:Stmt } while (B:BExp) => S ~> if(B){ do { S } while (B) } [structural]

    rule <k>
            for (I:Id in [ (V:Int, Vs:ListValues) ] ) { S:Stmt }
            => S ~> for (I in [ Vs:ListValues ] ) { S }
            ... 
        </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>
    
    rule <k>
            for (I:Id in [ (V:Int, Vs:ListValues) ] ) { S:Stmt }
            => S ~> for (I in [ Vs:ListValues ] ) { S }
            ... 
        </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>
        

    rule for (I:Id in [ .ListValues ] ) B:Block => Skip

    rule I1:Int + I2:Int => I1 +Int I2
    rule I1:Int - I2:Int => I1 -Int I2
    rule I1:Int * I2:Int => I1 *Int I2
    rule I1:Int / I2:Int => I1 /Int I2
    rule I1:Int < I2:Int => I1 <Int I2
    rule I1:Int <= I2:Int => I1 <=Int I2
    rule I1:Int == I2:Int => I1 ==Int I2
    rule I1:Int > I2:Int => I1 >Int I2

    rule <k> T:Type I:Id ; => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> T:Type (I:Id, Xs:Ids) ; => T Xs ; ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> T:Type (I:Id, Xs:Ids) = V:Int ; => T Xs = V ; ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    rule T:Type .Ids ; => Skip  
    rule T:Type .Ids = _:Int ; => Skip  

    rule <k> var I:Id = V:Int ; => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> I:Id = V:Int => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>

    rule <k> I1:Id = I2:Id => I1 = V ... </k>
        <env> ... I2 |-> L ... </env>
        <store> ... L |-> V  ... </store>

    rule <k> I:Id => V ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> V ... </store>

    rule <k> I:Id ++ => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (V => V +Int 1) ... </store>


    configuration <T> 
        <k> $PGM:Pgm </k>
        <env> .Map </env>
        <store> .Map </store>
        <loc> 1 </loc>
    </T>
 
endmodule

module KOTLIN
    import DOMAINS
    import KOTLIN-SYNTAX

    syntax KResult ::= Int | Bool
endmodule