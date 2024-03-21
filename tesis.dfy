//-------------------------------- MINIMALLY ANNOTATED PROGRAM -----------------------------------------
datatype Expresion = 
| L(number: int)
| Var(varName: string)
| sum(n1: Expresion, n2: Expresion)
| substract(n1: Expresion, n2: Expresion)
| mul(n1: Expresion, n2: Expresion)


datatype Condition =
  | K(boolean:bool)
  | Not(condition: Condition)
  | Imply(ConditonA: Condition, ConditonB: Condition) 
  | And(ConditonA: Condition, ConditonB: Condition) 
  | Substitution(substitution: map<string, Expresion>, condition: Condition)
  | Less(e1:Expresion, e2: Expresion)
  | Greater(e1:Expresion, e2: Expresion)
  | Equals(e1:Expresion, e2: Expresion)

datatype Program =
  | Assign(assignments: map<string, Expresion>)
  | Secuence(p1: Program, p2: Program)
  | If(condition: Condition, pThen: Program, pElse: Program)
  | While(pInvariant: Condition, condition: Condition, body: Program)

datatype Specification =
  | Instruction(precondition: Condition, program: Program, postcondition: Condition)

//HOORE TREES DATATYPE
datatype THoare =
    Assign(assignments:map<string,Expresion>, condition: Condition)
  | Secuence(tree1: THoare, tree2: THoare)
  | If(condition: Condition, tree1: THoare, tree2: THoare,cp:Condition)
  | While(pInvariant: Condition, condition: Condition, tree: THoare) 

//------------------------------------------------------------------------------------------------------
//--------------------------------------- CORRECTNESS ---------------------------------------------------

// function Correctness (three: THoare): (Specification, set<Condition>){
//   match three

//   case Assign(identifiers, condition) => (
//     Instruction(Condition.Substitution(identifiers),Program.Assign(identifiers),condition),{}
//   )
//   case If(condition, tree1, tree2,cp) => (
//       match Correctness(tree1)

//       case (s1,cs1) =>
//       match s1

//       case Instruction(pc1, p1, c1) => 
//         match Correctness(tree2)

//         case (s2,cs2) => 
//           match s2
//           case Instruction(pc2, p2, c2) => (Instruction(And(Imply(condition,pc1),Imply(Not(condition),pc2)),Program.If(condition,p1,p2,cp),cp),(cs1 + cs2 + {Imply(pc1,cp),Imply(pc2,cp)})))
  
//   case While(pInvariant, condition, tree) => (
//       match Correctness(tree)

//       case (s,cs) => 
//         match s
//         case Instruction(pc, p, c) => (Instruction(pInvariant,Program.While(pInvariant,condition,p),And(pInvariant,Not(condition))),cs + {Imply(And(pInvariant,condition),pc),Imply(c,pInvariant)}))
//   case Secuence(tree1, tree2) => (
//       match Correctness(tree1)

//       case (s1,cs1) => 
//         match s1

//         case Instruction(pc1, p1, c1) => 
//           match Correctness(tree2)

//           case (s2,cs2) => 
//             match s2
//             case Instruction(pc2, p2, c2) => (Instruction(pc1,Program.Secuence(p1,p2),c2),(cs1 + cs2 + {c1} + {pc2})))

// }

//------------------------------------------------------------------------------------------------------
//--------------------------------------- VCG ----------------------------------------------------------

function VCG (specification: Specification): (multiset<Condition>){
  match specification

  case Instruction(precondition, program, postcondition) => (
    match VCGP(program,postcondition)

    case (c,cs) => (
      (cs + multiset{Imply(precondition,c)})
      )
    )

}

function VCGP (program: Program, postcondition: Condition): (Condition,multiset<Condition>)
ensures var result := VCGP(program,postcondition) ; Hoare(Instruction(result.0,program,postcondition),result.1)
decreases program
{
  match program
  case Assign(assignments) => (Condition.Substitution(assignments,postcondition),multiset{})
  case Secuence(p1, p2) => (
    match VCGP(p2, postcondition)

    case (c1,cs1) => (
      match VCGP(p1, c1)

      case (c2,cs2) => assert Hoare(Instruction(c2, p1, c1), cs2); assert Hoare(Instruction(c1, p2, postcondition), cs1); (c2,cs2 + cs1)))
      
  case If(condition, p1, p2) => (
    match VCGP(p1, postcondition)

    case (c1,cs1) => 
      match VCGP(p2, postcondition)

      case (c2,cs2) => var q := And(Imply(condition,c1),Imply(Not(condition),c2)); 
      assert Hoare(Instruction(And(q, condition), p1, postcondition), cs1 + multiset{Imply(And(q, condition),c1)});
      assert Hoare(Instruction(And(q, Not(condition)), p2, postcondition), cs2 + multiset{Imply(And(q, Not(condition)),c2)});
      (q,(cs1 + multiset{Imply(And(q,condition),c1)}) + (cs2 + multiset{Imply(And(q,Not(condition)),c2)}))
      )
  case While(pInvariant, condition, body) => (
    match VCGP(body, pInvariant)

    case (c,cs) => (
      pInvariant,
      cs + multiset{
        Imply(And(pInvariant,condition),c)
        } +
        multiset{
        Imply(And(pInvariant,Not(condition)),postcondition)
        }
        )
    )
}


ghost predicate Hoare(prog: Specification, vcs: multiset<Condition>)

decreases var Instruction(precondition, program, postcondition)  := prog ; program, |vcs|

{
  (match prog
  case Instruction(precondition, program, postcondition) => (
    match program
    case Assign(assignments) => (
      precondition == Condition.Substitution(assignments,postcondition) && vcs == multiset{}
    )
    case Secuence(p1, p2) => (
      exists s,vcs1,vcs2 :: Hoare(Instruction(precondition, p1, s), vcs1) && Hoare(Instruction(s, p2, postcondition), vcs2) && vcs == vcs1 + vcs2
    )
    case If(condition, p1, p2) => (
      exists vcs1,vcs2 :: Hoare(Instruction(And(precondition,condition), p1, postcondition), vcs1) && 
      Hoare(Instruction(And(precondition,Not(condition)), p2, postcondition), vcs2) && vcs == vcs1 + vcs2
    )
    case While(inv, b, p) => (
       Hoare(Instruction(And(inv,b),p,inv),vcs) && (precondition == inv) && (postcondition == And(inv,Not(b)))
    )
  )
  || (exists qP,vcs1 :: vcs == vcs1 + multiset{Imply(precondition,qP)} && assert |vcs1| < |vcs|; Hoare(Instruction(qP,program,postcondition),vcs1))
  || (exists rP,vcs1 :: vcs == vcs1 + multiset{Imply(rP,postcondition)} && assert |vcs1| < |vcs|;Hoare(Instruction(precondition,program,rP),vcs1))
  )
  
}