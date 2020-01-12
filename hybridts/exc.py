class TypeCheckError(Exception):
    pass


class IllFormedType(TypeCheckError):
    form: str

    def __init__(self, form):
        self.form = form


class RowFieldDuplicated(TypeCheckError):
    def __init__(self, field: str):
        self.field = field


class TypeMismatch(TypeCheckError):
    lhs: object
    rhs: object

    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

class ForallVarExceedScope(TypeCheckError):
    forall_scope: object
    var: object
    def __init__(self, scope, var):
        self.forall_scope = scope
        self.var = var
