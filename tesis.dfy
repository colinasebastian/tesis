//-------------------------------- MINIMALLY ANNOTATED PROGRAM -----------------------------------------

datatype Condition =
    True() // ver como asignarle el tipo true y false
  | False()
  | Not(boolean: bool)
  | Imply(ConditonA: Condition, ConditonB: Condition) 
  | And(ConditonA: Condition, ConditonB: Condition) 
  | Substitution(identifiers: array<string>, values: array<int>, state: map<string, int>) // revisar

datatype Instruction =
    Assign(identifiers: array<string>, values: array<int>, state: map<string, int>)
  | Secuence(instructions: Program, instruction: Instruction)
  | If(condition: Condition, pThen: Program, pElse: Program)
  | While(pInvariant: bool, condition: Condition, body: Program)

datatype Program =
  | Skip // Represents a null instruction or the termination of the program.
  // precondition == require
  // postcondition == ensure  
  | Instruction(precondition: bool, instruction: Instruction, postcondition: bool)
  // revisar precondiciones si es bool o algo mas

//HOORE TREES DATATYPE
datatype THoore =
    Assign(identifiers: array<string>, values: array<int>, condition: Condition)
    // revisar el caso de la condition porque tato habla de una postcondicion
  | Secuence(tree1: THoore, tree2: THoore)
  | If(condition: Condition, tree1: THoore, tree2: THoore)
  | While(pInvariant: bool, condition: Condition, tree: THoore) 

//CORRECTNESS DATATYPE
//datatype Correct =
//tomo un arbol y retorno la conclusion y condiciones





//AUXILIARY DATATYPES
datatype KeyValuePair<K, V> = KeyValuePair {
    Key: K,
    Value: V
}


/////////////PREGUNTAS
//La invariante es una condition?? en el while surge la duda


//------------------------------------------------------------------------------------------------------
//--------------------------------------- HOORE TREES --------------------------------------------------

  function Assign(ids: array<string>, values: array<int>, state: seq<KeyValuePair<string, int>>)
  requires ids.Length == values.Length // Asegura que las listas tengan la misma longitud
{
  var i := 0;
  while i < ids.Length
    invariant 0 <= i < ids.Length
  {
    state[ids[i]] := values[i];
    i := i + 1;
  }
}

//------------------------------------------------------------------------------------------------------
//--------------------------------------- CORRECTNES ---------------------------------------------------

function Correctness (three: THoore):  (result: KeyValuePair<Program, seq<Condition>>)
// revisar el caso de seq<condition> porque es la "C"
  match three

  case Assign(identifiers, values, condition) => {
        // Realizar acciones para el caso de Assign
      // Puedes acceder a identifiers, values y condition aquí


  }
  case Secuence(tree1, tree2) => {
      // Realizar acciones para el caso de Secuence
      // Puedes acceder a tree1 y tree2 aquí

  }
  case If(condition, tree1, tree2) => {
      // Realizar acciones para el caso de If
      // Puedes acceder a condition, tree1 y tree2 aquí

  }
  case While(pInvariant, condition, tree) => {
      // Realizar acciones para el caso de While
      // Puedes acceder a pInvariant, condition y tree aquí

  }
  else {
      // Realizar acciones para casos no contemplados

  }

//------------------------------------------------------------------------------------------------------

//Example
method Main() {
    var dictionary: seq<KeyValuePair<string, int>> := new seq<KeyValuePair<string, int>>();
    
    // Agregar elementos al diccionario
    dictionary := dictionary + [KeyValuePair{Key: "Alice", Value: 30}];
    dictionary := dictionary + [KeyValuePair{Key: "Bob", Value: 25}];
    
    // Buscar un valor por clave
    var aliceAge := GetValueByKey(dictionary, "Alice");
    
    assert aliceAge == 30;
}

function GetValueByKey<K, V>(dict: seq<KeyValuePair<K, V>, key: K) returns (result: V)
    ensures forall(i | 0 <= i < |dict| :: dict[i].Key != key ==> dict[i].Value == old(dict[i].Value))
{
    result := default(V);
    var found := false;
    
    var i := 0;
    while i < |dict
        invariant 0 <= i <= |dict|
        invariant !found ==> (forall(j | 0 <= j < i :: dict[j].Key != key ==> dict[j].Value == old(dict[j].Value)))
    {
        if dict[i].Key == key {
            result := dict[i].Value;
            found := true;
        }
        i := i + 1;
    }
    
    assert found; // Asegurar que se encontró la clave
}