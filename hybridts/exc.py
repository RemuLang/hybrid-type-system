class IllFormedType(Exception):
    form: str

    def __init__(self, form):
        self.form = form


class UnboundTypeVar(Exception):
    var: str

    def __init__(self, var):
        self.var = var


class RowFieldDuplicated(Exception):
    def __init__(self, field: str):
        self.field = field


class TypeMismatch(Exception):
    lhs: object
    rhs: object

    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs
