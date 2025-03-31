import itertools


class Sentence():

    def evaluate(self, model):
        """Evaluates the logical sentence."""
        raise Exception("nothing to evaluate")

    def formula(self):
        """Returns string formula representing logical sentence."""
        return ""

    def symbols(self):
        """Returns a set of all symbols in the logical sentence."""
        return set()

    @classmethod
    def validate(cls, sentence):
        if not isinstance(sentence, Sentence):
            raise TypeError("must be a logical sentence")

    @classmethod
    def parenthesize(cls, s):
        """Parenthesizes an expression if not already parenthesized."""
        def balanced(s):
            """Checks if a string has balanced parentheses."""
            count = 0
            for c in s:
                if c == "(":
                    count += 1
                elif c == ")":
                    if count <= 0:
                        return False
                    count -= 1
            return count == 0
        if not len(s) or s.isalpha() or (
            s[0] == "(" and s[-1] == ")" and balanced(s[1:-1])
        ):
            return s
        else:
            return f"({s})"


class Symbol(Sentence):

    def __init__(self, name):
        self.name = name

    def __eq__(self, other):
        return isinstance(other, Symbol) and self.name == other.name

    def __hash__(self):
        return hash(("symbol", self.name))

    def __repr__(self):
        return self.name

    def evaluate(self, model):
        try:
            return bool(model[self.name])
        except KeyError:
            raise EvaluationException(f"variable {self.name} not in model")

    def formula(self):
        return self.name

    def symbols(self):
        return {self.name}


class Not(Sentence):
    def __init__(self, operand):
        Sentence.validate(operand)
        self.operand = operand

    def __eq__(self, other):
        return isinstance(other, Not) and self.operand == other.operand

    def __hash__(self):
        return hash(("not", hash(self.operand)))

    def __repr__(self):
        return f"Not({self.operand})"

    def evaluate(self, model):
        return not self.operand.evaluate(model)

    def formula(self):
        return "¬" + Sentence.parenthesize(self.operand.formula())

    def symbols(self):
        return self.operand.symbols()


class And(Sentence):
    def __init__(self, *conjuncts):
        for conjunct in conjuncts:
            Sentence.validate(conjunct)
        self.conjuncts = list(conjuncts)

    def __eq__(self, other):
        return isinstance(other, And) and self.conjuncts == other.conjuncts

    def __hash__(self):
        return hash(
            ("and", tuple(hash(conjunct) for conjunct in self.conjuncts))
        )

    def __repr__(self):
        conjunctions = ", ".join(
            [str(conjunct) for conjunct in self.conjuncts]
        )
        return f"And({conjunctions})"

    def add(self, conjunct):
        Sentence.validate(conjunct)
        self.conjuncts.append(conjunct)

    def evaluate(self, model):
        # AND es verdadero solo cuando TODOS los operandos son verdaderos.
        for conjunct in self.conjuncts:
            if not conjunct.evaluate(model):
                return False
        return True

    def formula(self):
        if len(self.conjuncts) == 1:
            return self.conjuncts[0].formula()
        return " ∧ ".join([Sentence.parenthesize(conjunct.formula())
                           for conjunct in self.conjuncts])

    def symbols(self):
        return set.union(*[conjunct.symbols() for conjunct in self.conjuncts])


class Or(Sentence):
    def __init__(self, *disjuncts):
        for disjunct in disjuncts:
            Sentence.validate(disjunct)
        self.disjuncts = list(disjuncts)

    def __eq__(self, other):
        return isinstance(other, Or) and self.disjuncts == other.disjuncts

    def __hash__(self):
        return hash(
            ("or", tuple(hash(disjunct) for disjunct in self.disjuncts))
        )

    def __repr__(self):
        disjuncts = ", ".join([str(disjunct) for disjunct in self.disjuncts])
        return f"Or({disjuncts})"

    def evaluate(self, model):
        # OR es verdadero si AL MENOS uno de los operandos es verdadero.
        for disjunct in self.disjuncts:
            if disjunct.evaluate(model):
                return True
        return False

    def formula(self):
        if len(self.disjuncts) == 1:
            return self.disjuncts[0].formula()
        return " ∨  ".join([Sentence.parenthesize(disjunct.formula())
                            for disjunct in self.disjuncts])

    def symbols(self):
        return set.union(*[disjunct.symbols() for disjunct in self.disjuncts])


class Implication(Sentence):
    def __init__(self, antecedent, consequent):
        Sentence.validate(antecedent)
        Sentence.validate(consequent)
        self.antecedent = antecedent
        self.consequent = consequent

    def __eq__(self, other):
        return (isinstance(other, Implication)
                and self.antecedent == other.antecedent
                and self.consequent == other.consequent)

    def __hash__(self):
        return hash(("implies", hash(self.antecedent), hash(self.consequent)))

    def __repr__(self):
        return f"Implication({self.antecedent}, {self.consequent})"

    def evaluate(self, model):
        # Una implicación es falsa solo si el antecedente es verdadero y el consecuente es falso.
        return (not self.antecedent.evaluate(model)) or self.consequent.evaluate(model)

    def formula(self):
        antecedent = Sentence.parenthesize(self.antecedent.formula())
        consequent = Sentence.parenthesize(self.consequent.formula())
        return f"{antecedent} => {consequent}"

    def symbols(self):
        return set.union(self.antecedent.symbols(), self.consequent.symbols())


class Biconditional(Sentence):
    def __init__(self, left, right):
        Sentence.validate(left)
        Sentence.validate(right)
        self.left = left
        self.right = right

    def __eq__(self, other):
        return (isinstance(other, Biconditional)
                and self.left == other.left
                and self.right == other.right)

    def __hash__(self):
        return hash(("biconditional", hash(self.left), hash(self.right)))

    def __repr__(self):
        return f"Biconditional({self.left}, {self.right})"

    def evaluate(self, model):
        # Bicondicional es verdadero si ambos lados tienen el mismo valor de verdad.
        return self.left.evaluate(model) == self.right.evaluate(model)

    def formula(self):
        left = Sentence.parenthesize(str(self.left))
        right = Sentence.parenthesize(str(self.right))
        return f"{left} <=> {right}"

    def symbols(self):
        return set.union(self.left.symbols(), self.right.symbols())


def model_check(knowledge, query):
    """Checks if the knowledge base entails the query.
    
    Es decir, verifica que en todos los modelos (asignaciones de valores de verdad)
    en los que el conocimiento (knowledge) es verdadero, la consulta (query) también lo sea.
    """
    
    def check_all(knowledge, query, symbols, model):
        """
        Función recursiva que evalúa si, dado un modelo parcial (con asignaciones para algunos símbolos),
        la base de conocimiento implica la consulta para todas las asignaciones posibles de los símbolos restantes.

        Parámetros:
        - knowledge: Oración que representa la base de conocimiento.
        - query: Oración cuya implicación se desea verificar.
        - symbols: Conjunto de símbolos que aún no han sido asignados en el modelo.
        - model: Diccionario que contiene las asignaciones actuales de valores de verdad a símbolos.

        Retorna:
        - True, si en todos los modelos extendidos la implicación se cumple.
        - False, en caso contrario.
        """
        # Caso base: No quedan símbolos por asignar.
        if not symbols:
            # Si la base de conocimiento es verdadera en el modelo actual...
            if knowledge.evaluate(model):
                # ...entonces, para que la implicación se cumpla, la consulta también debe ser verdadera.
                return query.evaluate(model)
            # Si la base de conocimiento es falsa, la implicación se cumple vacuamente.
            return True
        else:
            # Paso recursivo:
            # 1. Tomar un símbolo arbitrario del conjunto de símbolos sin asignar.
            remaining = symbols.copy()
            symbol = remaining.pop()
            
            # 2. Crear dos modelos: uno donde el símbolo se asigna a True y otro a False.
            model_true = model.copy()
            model_true[symbol] = True
            model_false = model.copy()
            model_false[symbol] = False
            
            # 3. Recursivamente, verificar la implicación para ambos modelos extendidos.
            # La base de conocimiento implica la consulta si se cumple en ambos casos.
            return (check_all(knowledge, query, remaining, model_true) and
                    check_all(knowledge, query, remaining, model_false))

    # Obtener el conjunto total de símbolos presentes tanto en la base de conocimiento como en la consulta.
    symbols = set.union(knowledge.symbols(), query.symbols())
    # Comenzar la verificación con un modelo vacío.
    return check_all(knowledge, query, symbols, dict())



if __name__ == "__main__":
    # símbolos
    A = Symbol("A")
    B = Symbol("B")
    C = Symbol("C")

    # Caso 1: Conocimiento: A ∧ B. Consultas: A, B, (A ∧ B) y (A ∨ B).
    kb1 = And(A, B)
    print("Caso 1:")
    print("¿kb1 implica A? ", model_check(kb1, A))           # Esperado: True
    print("¿kb1 implica B? ", model_check(kb1, B))           # Esperado: True
    print("¿kb1 implica (A ∧ B)? ", model_check(kb1, And(A, B)))  # Esperado: True
    print("¿kb1 implica (A ∨ B)? ", model_check(kb1, Or(A, B)))   # Esperado: True

    # Caso 2: Conocimiento: A ∨ B. Consulta: A.
    kb2 = Or(A, B)
    print("\nCaso 2:")
    print("¿kb2 implica A? ", model_check(kb2, A))           # Esperado: False
    # Explicación: existe un modelo en el que A es F y B es V, por lo que kb2 es verdadero
    # pero A es falso; por tanto, kb2 no implica A.

    # Caso 3: Conocimiento: A ∧ (A => B). Consulta: B.
    kb3 = And(A, Implication(A, B))
    print("\nCaso 3:")
    print("¿kb3 implica B? ", model_check(kb3, B))           # Esperado: True

    # Caso 4: Conocimiento: Bicondicional(A, B) junto con A. Consulta: B.
    kb4 = Biconditional(A, B)
    kb4_con_A = And(kb4, A)
    print("\nCaso 4:")
    print("¿(Bicondicional(A, B) ∧ A) implica B? ", model_check(kb4_con_A, B))  # Esperado: True

    # Caso 5: Conocimiento inconsistente (A ∧ ¬A). Consulta: cualquier fórmula (por vacuidad).
    kb5 = And(A, Not(A))
    print("\nCaso 5:")
    print("¿(A ∧ ¬A) implica B? ", model_check(kb5, B))       # Esperado: True
    # Explicación: Una base de conocimiento insatisfacible implica cualquier consulta
