from miasm.analysis.type_solver import *

class FunctionSignature:
    def __init__(self, ret, args) -> None:
        """
        @ret: return type of the function
        @args: array of arguments types
        """
        self.ret = ret
        self.args = args

    def __str__(self):
        return f"({','.join([arg for arg in self.args])}) -> {self.ret}"


class SignaturesDB:
    def __init__(self, loc_db) -> None:
        self.signatures = dict()
        self.loc_db = loc_db

    def add_signature(self, loc_key, fs):
        self.signatures[loc_key] = fs

    def get_signature(self, loc_key):
        return self.signatures[loc_key]

    def has_signature(self, loc_key):
        return loc_key in self.signatures

