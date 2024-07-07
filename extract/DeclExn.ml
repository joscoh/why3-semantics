exception UnboundVar of vsymbol
exception UnexpectedProjOrConstr of lsymbol
exception NoTerminationProof of lsymbol

exception IllegalTypeAlias of tysymbol
exception ClashIdent of ident
exception BadConstructor of lsymbol

exception BadRecordField of lsymbol
exception RecordFieldMissing of lsymbol
exception DuplicateRecordField of lsymbol

exception EmptyDecl
exception EmptyAlgDecl of tysymbol

exception NonPositiveTypeDecl of tysymbol * lsymbol * ty
