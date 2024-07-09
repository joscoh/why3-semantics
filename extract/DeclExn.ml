exception UnboundVar of vsymbol
exception UnexpectedProjOrConstr of lsymbol
exception NoTerminationProof of lsymbol

exception IllegalTypeAlias of tysymbol
exception ClashIdent of ident
exception BadLogicDecl of lsymbol * lsymbol
exception BadConstructor of lsymbol

exception BadRecordField of lsymbol
exception RecordFieldMissing of lsymbol
exception DuplicateRecordField of lsymbol

exception EmptyDecl
exception EmptyAlgDecl of tysymbol
exception EmptyIndDecl of lsymbol

exception NonPositiveTypeDecl of tysymbol * lsymbol * ty

exception InvalidIndDecl of lsymbol * prsymbol
exception NonPositiveIndDecl of lsymbol * prsymbol * lsymbol

exception KnownIdent of ident
exception UnknownIdent of ident
exception RedeclaredIdent of ident
