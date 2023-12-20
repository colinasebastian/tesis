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
  | Skip // revisar
  | Assign(assignments: map<string, Expresion>)
  | Secuence(instructions: Program, instruction: Program)
  | If(condition: Condition, pThen: Program, pElse: Program)
  | While(pInvariant: Condition, condition: Condition, body: Program)

datatype Specification =
  | Instruction(precondition: Condition, program: Program, postcondition: Condition)

//HOORE TREES DATATYPE
datatype THoare =
    Assign(assignments:map<string,Expresion>, condition: Condition)
    // revisar el caso de la condition porque tato habla de una postcondicion
  | Secuence(tree1: THoare, tree2: THoare)
  | If(condition: Condition, tree1: THoare, tree2: THoare)
  | While(pInvariant: Condition, condition: Condition, tree: THoare) 

//------------------------------------------------------------------------------------------------------
//--------------------------------------- CORRECTNES ---------------------------------------------------

function Correctness (three: THoare): (Specification, seq<Condition>){
  match three

  case Assign(identifiers, condition) => (
    Instruction(Condition.Substitution(identifiers),Program.Assign(identifiers),condition),[]
  )
  case If(condition, tree1, tree2) => (
      match Correctness(tree1)

      case (s1,cs1) =>
      match s1

      case Instruction(pc1, p1, c1) => 
        match Correctness(tree2)

        case (s2,cs2) => 
          match s2
          // revisar c2 (c prima) del if (mirar imagen)
          // revisar concatenacion de condiciones con las de la imagen teniendo en cuenta q implique el c2 anterior
          case Instruction(pc2, p2, c2) => (Instruction(And(Imply(condition,pc1),Imply(Not(condition),pc2)),Program.If(condition,p1,p2),c2),(cs1 + cs2 + [pc1] + [pc2])))
  
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
            //el secuence tiene que ser de program o de thoare??
            case Instruction(pc2, p2, c2) => (Instruction(pc1,Program.Secuence(p1,p2),c2),(cs1 + cs2 + [c1] + [pc2])))

}

//------------------------------------------------------------------------------------------------------
//--------------------------------------- VCG ----------------------------------------------------------

// debreiamos llamar a correctness en algun momento?

function VCG (specification: Specification): seq<Condition>{
  match specification

  case Instruction(precondition, program, postcondition) => VCGP(program,postcondition)


    // case Skip => [precondition]
    // case Assign(assignments) => [precondition]
    // case Secuence(instructions, instruction) => (
    //   match VCG(Instruction(precondition, instructions, postcondition))

    //   case cs1 => 
    //     match VCG(Instruction(cs1, instruction, postcondition))

    //     case cs2 => cs2)
    // case If(condition, pThen, pElse) => (
    //   match VCG(Instruction(And(precondition,condition), pThen, postcondition))

    //   case cs1 => 
    //     match VCG(Instruction(And(precondition,Not(condition)), pElse, postcondition))

    //     case cs2 => cs1 + cs2)
    // case While(pInvariant, condition, body) => (
    //   match VCG(Instruction(And(precondition,pInvariant), body, pInvariant))

    //   case cs1 => [Imply(And(precondition, pInvariant), cs1)])
}

function VCGP (program: Program, postcondition: Condition): seq<Condition>{
  match program

  case Skip => [postcondition]
  case Assign(assignments) => [postcondition]
  case Secuence(instructions, instruction) => (
    match VCGP(instructions, postcondition)

    case cs1 => 
      match VCGP(instruction, cs1)

      case cs2 => cs2)
  case If(condition, pThen, pElse) => (
    match VCGP(pThen, postcondition)

    case cs1 => 
      match VCGP(pElse, postcondition)

      case cs2 => cs1 + cs2)
  case While(pInvariant, condition, body) => (
    match VCGP(body, pInvariant)

    case cs1 => [Imply(And(pInvariant, condition), cs1)])
}