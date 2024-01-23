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
  | Substitution(substitution: map<string, Expresion>)
  | Less(e1:Expresion, e2: Expresion)
  | Greater(e1:Expresion, e2: Expresion)
  | Equals(e1:Expresion, e2: Expresion)

datatype Program =
  // | Skip // revisar
  | Assign(assignments: map<string, Expresion>)
  | Secuence(instructions: Program, instruction: Program)
  | If(condition: Condition, pThen: Program, pElse: Program,cp:Condition)
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

function Correctness (three: THoare): (Specification, seq<Condition>){
  match three

  case Assign(identifiers, condition) => (
    Instruction(Condition.Substitution(identifiers),Program.Assign(identifiers),condition),[]
  )
  case If(condition, tree1, tree2,cp) => (
      match Correctness(tree1)

      case (s1,cs1) =>
      match s1

      case Instruction(pc1, p1, c1) => 
        match Correctness(tree2)

        case (s2,cs2) => 
          match s2
          case Instruction(pc2, p2, c2) => (Instruction(And(Imply(condition,pc1),Imply(Not(condition),pc2)),Program.If(condition,p1,p2,cp),cp),(cs1 + cs2 + [Imply(pc1,cp),Imply(pc2,cp)])))
  
  case While(pInvariant, condition, tree) => (
      match Correctness(tree)

      case (s,cs) => 
        match s
        case Instruction(pc, p, c) => (Instruction(pInvariant,Program.While(pInvariant,condition,p),And(pInvariant,Not(condition))),cs + [Imply(And(pInvariant,condition),pc),Imply(c,pInvariant)]))
  case Secuence(tree1, tree2) => (
      match Correctness(tree1)

      case (s1,cs1) => 
        match s1

        case Instruction(pc1, p1, c1) => 
          match Correctness(tree2)

          case (s2,cs2) => 
            match s2
            case Instruction(pc2, p2, c2) => (Instruction(pc1,Program.Secuence(p1,p2),c2),(cs1 + cs2 + [c1] + [pc2])))

}

//------------------------------------------------------------------------------------------------------
//--------------------------------------- VCG ----------------------------------------------------------

function VCG (specification: Specification): (THoare,seq<Condition>){
  match specification

  case Instruction(precondition, program, postcondition) => (
    match VCGP(program,postcondition)

    case (c,th,cs) => (th,cs + [Imply(precondition,postcondition)])
    )

}

function VCGP (program: Program, postcondition: Condition): (Condition,THoare,seq<Condition>){
  match program
  case Assign(assignments) => (Condition.Substitution(assignments),THoare.Assign(assignments,postcondition),[])
  case Secuence(instructions, instruction) => (
    match VCGP(instructions, postcondition)

    case (c1,th1,cs1) => 
      match VCGP(instruction, c1)

      case (c2,th2,cs2) => (c2,THoare.Secuence(th1,th2),cs1 + cs2))
  case If(condition, pThen, pElse,cp) => (
    match VCGP(pThen, postcondition)

    case (c1,th1,cs1) => 
      match VCGP(pElse, postcondition)

      case (c2,th2,cs2) => (And(Imply(condition,c1),Imply(Not(condition),c2)),THoare.If(condition,th1,th2,cp),cs1 + cs2)
      )
  case While(pInvariant, condition, body) => (
    match VCGP(body, pInvariant)

    case (c,th,cs) => (pInvariant,THoare.While(pInvariant,condition,th),cs + [Imply(And(pInvariant,condition),c),Imply(And(pInvariant,Not(condition)),postcondition)])
    )
}


lemma VCGCorrectness: forall (specification: Specification) :: Correctness(VCG(specification)) == specification
  proof
    forall (specification: Specification) :: 
      match Correctness(VCG(specification))
      case (s,cs) => 
        match s
        case Instruction(precondition, program, postcondition) => 
          match VCG(specification)
          case (th,cs2) => 
            match th
            case THoare.Assign(assignments, postcondition) => 
              (Instruction(precondition, program, postcondition),cs + cs2)
            case THoare.Secuence(tree1, tree2) => 
              (Instruction(precondition, program, postcondition),cs + cs2)
            case THoare.If(condition, tree1, tree2,cp) => 
              (Instruction(precondition, program, postcondition),cs + cs2)
            case THoare.While(pInvariant, condition, tree) => 
              (Instruction(precondition, program, postcondition),cs + cs2)
  qed