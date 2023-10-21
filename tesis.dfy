datatype Instruction =
  | Asign(id: string, value: int)
  | Secuence(instructions: Program, instruction: Instruction)
  | Selection(condition: bool, pThen: Program, pElse: Program)
  | Iteration(condition: bool, body: Program)

datatype Program =
  | Skip // Representa una instrucción nula o la terminación del programa.
  | Instruction(instruction: Instruction)