
/// An unknown value based purely on identity.
class Variable: CustomStringConvertible, Hashable {
    var description: String { return ObjectIdentifier(self).debugDescription }
    var hashValue: Int { return ObjectIdentifier(self).hashValue }
}

func ==(lhs: Variable, rhs: Variable) -> Bool {
    return lhs === rhs
}

/// An item that can be compared with miniKanren.
indirect enum Term<Value: Hashable>: CustomStringConvertible, Hashable {
    /// An unknown value.
    case variable(Variable)
    /// A concrete value.
    case value(Value)
    /// A pair of terms, which can be used to construct larger values.
    case pair(Term<Value>, Term<Value>)
    /// An empty term, used to terminate lists made of terms.
    case empty
    /// A reified variable that has no value.
    case symbol(Int)
    
    var description: String {
        switch self {
        case let .variable(v):       return v.description
        case let .value(v):          return "\(v)"
        case let .pair(left, right): return "(\(left), \(right))"
        case .empty:                 return "()"
        case let .symbol(n):         return "_\(n)"
        }
    }
    
    /// Construct a term representing a list of terms.
    init<C: Collection>(_ collection: C) where C.Iterator.Element == Term<Value> {
        var iterator = collection.reversed().makeIterator()
        var term = Term.empty
        while let next = iterator.next() {
            term = Term.pair(next, term)
        }
        self = term
    }
    
    var hashValue: Int {
        switch self {
        case let .variable(v):
            return v.hashValue
        case let .value(v):
            return v.hashValue
        case let .pair(left, right):
            return left.hashValue ^ right.hashValue
        case .empty:
            return 0
        case let .symbol(n):
            return n
        }
    }
}

extension Term: ExpressibleByArrayLiteral {
    /// Easily create a list term from an array literal.
    init(arrayLiteral elements: Term<Value>...) {
        self = .init(elements)
    }
}

func == <Value>(lhs: Term<Value>, rhs: Term<Value>) -> Bool {
    switch (lhs, rhs) {
    case let (.variable(lhs), .variable(rhs)):
        return lhs == rhs
    case let (.value(lhs), .value(rhs)):
        return lhs == rhs
    case let (.pair(lhs1, lhs2), .pair(rhs1, rhs2)):
        return lhs1 == rhs1 && lhs2 == rhs2
    case (.empty, .empty):
        return true
    default:
        return false
    }
}

struct UnificationError: Error { }

/// A state is a set of assocations and a counter representing the next variable.
struct State<Value: Hashable> {
    /// A goal--something that takes an initial state and returns an iterator
    /// of all the states that can be achieved by meeting that goal.
    typealias Goal = (State<Value>) -> AnyIterator<State<Value>>
    
    /// Known assocations between variables and other terms (e.g., x=5 or x=y).
    var substitution: [(Variable, Term<Value>)] = []
    
    init() { }
    
    /// `occurs√` in miniKanren
    /// Returns whether x==v would introduce a circular definition.
    func occurs(_ x: Variable, _ v: Term<Value>) -> Bool {
        let v = walk(v)
        switch v {
        case let .variable(v):
            return v == x
        case let .pair(left, right):
            return occurs(x, left) || occurs(x, right)
        default:
            return false
        }
    }
    
    /// `ext-s-no-check` in miniKanren
    /// Extend the state by adding another variable -> term assocation without
    /// checking whether it would introduce a circular reference..
    func extendNoCheck(_ variable: Variable, _ value: Term<Value>) -> State {
        var state = self
        state.substitution.append((variable, value))
        return state
    }
    
    /// `ext-s` in miniKanren
    /// Extend the state by adding another variable -> term assocation.
    func extend(_ variable: Variable, _ value: Term<Value>) throws -> State {
        if occurs(variable, value) {
            throw UnificationError()
        }
        return extendNoCheck(variable, value)
    }
    
    /// `walk` in miniKanren
    /// Look up the value of a term in the state.
    func walk(_ term: Term<Value>) -> Term<Value> {
        if case let .variable(v) = term, let (_, value) = substitution.first(where: { $0.0 == v }) {
            return walk(value)
        }
        return term
    }
    
    /// `walk*` in miniKanren
    /// Look up the value of a term in the state, descending into the term if
    /// it's a pair.
    func walkStar(_ v: Term<Value>) -> Term<Value> {
        let v = walk(v)
        if case let .pair(car, cdr) = v {
            return .pair(walkStar(car), walkStar(cdr))
        }
        return v
    }
    
    /// `unify` in miniKanren
    /// Attempt to unify two terms in the state--i.e., make them equivalent. If
    /// the terms can't be unified, throws a UnificationError.
    func unify(_ u: Term<Value>, _ v: Term<Value>) throws -> State {
        let u = walk(u)
        let v = walk(v)
        
        if u == v { return self }
        
        switch (u, v) {
        case let (.variable(u), .variable(v)):
            return extendNoCheck(u, .variable(v))
        case let (.variable(u), _):
            return try extend(u, v)
        case let (_, .variable(v)):
            return try extend(v, u)
        case let (.pair(u1, u2), .pair(v1, v2)):
            return try unify(u1, v1).unify(u2, v2)
        default:
            throw UnificationError()
        }
    }
    
    /// `reify` in miniKanren
    /// Turn a term into a value by replacing all variables with values or symbols.
    func reify(_ v: Term<Value>) -> Term<Value> {
        let v = walkStar(v)
        return State().reifyS(v).walkStar(v)
    }
    
    /// `reify-s` in miniKanren
    /// Walks through a term, replacing each variable with its value or a symbol.
    func reifyS(_ v: Term<Value>) -> State {
        let v = walk(v)
        switch v {
        case let .variable(v):
            return extendNoCheck(v, .symbol(substitution.count))
        case let .pair(car, cdr):
            return reifyS(car).reifyS(cdr)
        default:
            return self
        }
    }
}

infix operator ≡ : ComparisonPrecedence

/// `≡` in miniKanren
/// A new goal that tries to make two terms equal.
func ≡ <Value>(lhs: Term<Value>, rhs: Term<Value>) -> State<Value>.Goal {
    return { state in
        do {
            return AnyIterator(values: [ try state.unify(lhs, rhs) ])
        } catch {
            return AnyIterator(values: [])
        }
    }
}

/// `≡` in miniKanren
/// Overload to make comparing variables easier.
func ≡ <Value>(lhs: Variable, rhs: Variable) -> State<Value>.Goal {
    return .variable(lhs) ≡ .variable(rhs)
}

/// `≡` in miniKanren
/// Overload to make comparing a variable and a value easier.
func ≡ <Value>(lhs: Variable, rhs: Value) -> State<Value>.Goal {
    return .variable(lhs) ≡ .value(rhs)
}

/// `≡` in miniKanren
/// Overload to make comparing a variable and a value easier.
func ≡ <Value>(lhs: Value, rhs: Variable) -> State<Value>.Goal {
    return .value(lhs) ≡ .variable(rhs)
}

/// A goal that succeeds when both goals succeed.
func && <Value>(lhs: State<Value>.Goal, rhs: State<Value>.Goal) -> State<Value>.Goal {
    return { state in lhs(state).flatMap(rhs) }
}

/// `cond^e` in miniKanren
/// A goal that succeeds when any goal succeeds.
func condE<Value>(_ goals: [State<Value>.Goal]) -> State<Value>.Goal {
    return { state in AnyIterator.interleave(goals.map { $0(state) }) }
}

/// `exist` in miniKanren
/// A goal that succeeds when all goals succeed.
func exist<Value>(_ block: (Variable) -> [State<Value>.Goal]) -> State<Value>.Goal {
    let goals = block(Variable())
    return { state in
        let initial = AnyIterator<State<Value>>(values: [ state ])
        return goals.reduce(initial) { $0.flatMap($1) }
    }
}

/// `exist` in miniKanren
/// A goal that succeeds when all goals succeed.
func exist<Value>(_ block: (Variable, Variable) -> [State<Value>.Goal]) -> State<Value>.Goal {
    let goals = block(Variable(), Variable())
    return { state in
        let initial = AnyIterator<State<Value>>(values: [ state ])
        return goals.reduce(initial) { $0.flatMap($1) }
    }
}

/// `exist` in miniKanren
/// A goal that succeeds when all goals succeed.
func exist<Value>(_ block: (Variable, Variable, Variable) -> [State<Value>.Goal]) -> State<Value>.Goal {
    let goals = block(Variable(), Variable(), Variable())
    return { state in
        let initial = AnyIterator<State<Value>>(values: [ state ])
        return goals.reduce(initial) { $0.flatMap($1) }
    }
}

/// `run` in miniKanren
/// Produce `n` solutions to a given goal.
func run<Value>(_ n: Int, block: (Variable) -> (State<Value>.Goal)) -> [Term<Value>] {
    let variable = Variable()
    return block(variable)(State())
        .prefix(n)
        .map { $0.reify(.variable(variable)) }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////

// A goal that demonstrates some basic logic.
run(2) { q -> State<Int>.Goal in
    return exist { x, z -> [State<Int>.Goal] in
        return [ x ≡ z, 3 ≡ z, q ≡ x ]
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////

// A goal that demonstrates alternation.
let values = run(5) { (q: Variable) -> State<Character>.Goal in
    return exist { (x: Variable, y: Variable, z: Variable) -> [State<Character>.Goal] in
        let goals: [State<Character>.Goal] = [
            "a" ≡ x && "1" ≡ y && "d" ≡ z,
            "2" ≡ y && "b" ≡ x && "e" ≡ z,
            "f" ≡ z && "c" ≡ x && "3" ≡ y
        ]
        return [
            condE(goals),
            [ .variable(x), .variable(y), .variable(z) ] ≡ .variable(q)
        ]
    }
}
print(values)
