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
  | Substitution(substitution: map<string, Expresion>) // revisar
  | Less(e1:Expresion, e2: Expresion)
  | Greater(e1:Expresion, e2: Expresion)
  | Equals(e1:Expresion, e2: Expresion)

datatype Program =
  | Skip // Represents a null instruction or the termination of the program.
  | Assign(assignments: map<string, Expresion>)
  | Secuence(instructions: Program, instruction: Program)
  | If(condition: Condition, pThen: Program, pElse: Program)
  | While(pInvariant: Condition, condition: Condition, body: Program)

datatype Specification =
  // precondition == require
  // postcondition == ensure  
  | Instruction(precondition: Condition, program: Program, postcondition: Condition)
  // revisar precondiciones si es bool o algo mas

//HOORE TREES DATATYPE
datatype THoare =
    Assign(assignments:map<string,Expresion>, condition: Condition)
    // revisar el caso de la condition porque tato habla de una postcondicion
  | Secuence(tree1: THoare, tree2: THoare)
  | If(condition: Condition, tree1: THoare, tree2: THoare)
  | While(pInvariant: Condition, condition: Condition, tree: THoare) 
  // caso del programa habria que agregarlo?

//CORRECTNESS DATATYPE
//datatype Correct =
//tomo un arbol y retorno la conclusion y condiciones





//AUXILIARY DATATYPES
datatype KeyValuePair<K, V> = KeyValuePair (
    Key: K,
    Value: V
)


/////////////PREGUNTAS
//La invariante es una condition?? en el while surge la duda


//------------------------------------------------------------------------------------------------------
//--------------------------------------- HOORE TREES --------------------------------------------------

//   function Assign(ids: array<string>, values: array<Expresion>, state: seq<KeyValuePair<string, Expresion>>): void
//   requires ids.Length == values.Length // Asegura que las listas tengan la misma longitud
// {
//   var i: int := 0;
//   while (i < ids.Length)
//     invariant 0 <= i < ids.Length
//   {
//     state[ids[i]] := values[i];
//     i := i + 1;
//   }
// }

//------------------------------------------------------------------------------------------------------
//--------------------------------------- CORRECTNES ---------------------------------------------------

method HeadTail (s: seq<Specification>) returns (x:Specification,xs:seq<Specification>){
    if |s| > 0 {
        return s[0], s[1 ..];
    } else {
        // Handle the case when the sequence is empty
        // In this case, return a default value for the type T and an empty sequence
        if |s| == 0 {
          return Instruction(K(true),Skip,K(true)), [Instruction(K(true),Skip,K(true))]; // revisar
        }
        
    }
}

function Correctness (three: THoare): (seq<Specification>, seq<Condition>){
// revisar el caso de seq<condition> porque es la "C"

  match three

  case Assign(identifiers, condition) => ([], [condition])
        // Realizar acciones para el caso de Assign
      // Puedes acceder a identifiers, values y condition aquí
  case If(condition, tree1, tree2) => ([],[condition])
      // Realizar acciones para el caso de If
      // Puedes acceder a condition, tree1 y tree2 aquí  
  case While(pInvariant, condition, tree) => ([],[condition])
      // Realizar acciones para el caso de While
      // Puedes acceder a pInvariant, condition y tree aquí
  case Secuence(tree1, tree2) => 
      // Realizar acciones para el caso de Secuence
      // Puedes acceder a tree1 y tree2 aquí
      match Correctness(tree1)

      case (s1,cs1) => 
        if(|s1|>0) then
        match s1[0] // revisar

        case Instruction(pc1, p1, c1) => 
          match Correctness(tree2)

          case (s2,cs2) => 
          if(|s2|>0) then
            match s2[0]

            case Instruction(pc2, p2, c2) => ((s1 + s2),(cs1 + cs2 + [c1] + [c2]))

      else (s1, cs1 + cs2 + [c1])
      else ([], [])
}
//------------------------------------------------------------------------------------------------------

//Example
// method Main() {
//     var dictionary: seq<KeyValuePair<string, int>> := new seq<KeyValuePair<string, int>>();
    
//     // Agregar elementos al diccionario
//     dictionary := dictionary + [KeyValuePair{Key: "Alice", Value: 30}];
//     dictionary := dictionary + [KeyValuePair{Key: "Bob", Value: 25}];
    
//     // Buscar un valor por clave
//     var aliceAge := GetValueByKey(dictionary, "Alice");
    
//     assert aliceAge == 30;
// }

// function GetValueByKey<K, V>(dict: seq<KeyValuePair<K, V>, key: K) returns (result: V)
//     ensures forall(i | 0 <= i < |dict| :: dict[i].Key != key ==> dict[i].Value == old(dict[i].Value))
// {
//     result := default(V);
//     var found := false;
    
//     var i := 0;
//     while i < |dict
//         invariant 0 <= i <= |dict|
//         invariant !found ==> (forall(j | 0 <= j < i :: dict[j].Key != key ==> dict[j].Value == old(dict[j].Value)))
//     {
//         if dict[i].Key == key {
//             result := dict[i].Value;
//             found := true;
//         }
//         i := i + 1;
//     }
    
//     assert found; // Asegurar que se encontró la clave
// }