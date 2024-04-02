open TermDefs

exception UncoveredVar of vsymbol
exception DuplicateVar of vsymbol

exception BadArity of lsymbol * BigInt.t
exception FunctionSymbolExpected of lsymbol
exception PredicateSymbolExpected of lsymbol
exception ConstructorExpected of lsymbol

