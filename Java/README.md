# Java stella-implementation-assignment

This is the skeleton for a Java implementation of the Stella programming language interpreter.

### Requirements

This was tested with:

* make 4.1
* BNFC 2.9.4.1
* antlr 4.12.0
* openjdk 17.0.6

### Building and running the interpreter

1. To build the interpreter run:

```sh
make
```

This typically involves running BNFC converter, and compiling the project in the chosen language,
resulting in a class file `src/interpret.class` that you can now use to type check and interpret programs.

2. Now, to run the type checker:

```sh
make typecheck
```

This starts the type checker waiting to input the program. Note that it will accept input until it encounters the end of file (Ctrl+D).

3. To run the interpreter:

```sh
make interpret <filename>
```

This starts the interpreter reading the program from the input file and waiting for the input of the argument for the _main_ function.

### Code Structure

[src/Interpret.java](src/Interpret.java) is the main file that contains the logic for reading a program and its arguments (if you run an interpreter).

[src/compiler/TypeCheck.java](src/compiler/TypeCheck.java) file assumes the content of the type checker logic. Currently they contain only prototypes of the functions for further implementation.
The input program from the interpreter is passed directly to the `typecheck` function.

[src/compiler/Eval.java](src/compiler/Eval.java) file similarly implies the logic of interpreting the program. They also contain only prototypes. The input program (read from the file) and the argument (entered after the interpreter starts) are passed directly to the `evalMainWith` function.

### How to develop

You must extend the existing files to perform the required actions.
If you need to add additional files, add them to [src/compiler](src/compiler/) folder to include them in the build process. Or create a new package in the [src](src/) folder. 
