open TermDefs

exception UncoveredVar of vsymbol
exception DuplicateVar of vsymbol

exception BadArity of lsymbol * BigInt.t
exception FunctionSymbolExpected of lsymbol
exception PredicateSymbolExpected of lsymbol
exception ConstructorExpected of lsymbol

exception TermExpected of term
exception FmlaExpected of term

(*TODO: move*)
exception AssertFail of string

exception InvalidIntegerLiteralType of ty
exception InvalidRealLiteralType of ty
exception InvalidStringLiteralType of ty
