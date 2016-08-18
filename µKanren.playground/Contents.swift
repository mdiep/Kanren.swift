
/// An unknown value.
struct Variable: CustomStringConvertible, Hashable {
    /// A number determines the variable's identity.
    let index: UInt
    
    var description: String { return "#\(index)" }
    var hashValue: Int { return Int(index) }
}

func ==(lhs: Variable, rhs: Variable) -> Bool {
    return lhs.index == rhs.index
}

/// An item that can be compared with µKanren.
indirect enum Term<Value: Equatable>: CustomStringConvertible, Equatable {
    /// An known value.
    case variable(Variable)
    /// A concrete value.
    case value(Value)
    /// A pair of terms, which can be used to construct larger values.
    case pair(Term<Value>, Term<Value>)
    /// An empty term, used to terminate lists made of terms.
    case empty
    
    var description: String {
        switch self {
        case let .variable(v):       return v.description
        case let .value(v):          return "\(v)"
        case let .pair(left, right): return "(\(left), \(right))"
        case .empty:                 return "()"
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

/// Error used with `State.unify()` fails to unify.
struct UnificationError: Error { }

/// A state is a set of assocations and a counter representing the next variable.
struct State<Value: Equatable>: CustomStringConvertible {
    /// A goal--something that takes an initial state and returns an iterator
    /// of all the states that can be achieved by meeting that goal.
    typealias Goal = (State<Value>) -> AnyIterator<State<Value>>
    
    /// Known assocations between variables and other terms (e.g., x=5 or x=y).
    var substitution: [Variable: Term<Value>] = [:]
    
    /// The index of the next unused variable.
    var counter: UInt = 0
    
    var variables: [Variable] {
        return (0..<counter).map { Variable(index: $0) }
    }
    
    var description: String {
        return variables
            .map { v in
                let value = walk(.variable(v))
                if .variable(v) == value {
                    return "\(v)"
                } else {
                    return "\(v) = \(value)"
                }
            }
            .joined(separator: ", ")
    }
    
    /// `ext-s` in µKanren
    /// Extend the state by adding another variable -> term assocation.
    func extend(_ variable: Variable, _ term: Term<Value>) -> State {
        var state = self
        state.substitution[variable] = term
        return state
    }
    
    /// `walk` in µKanren
    /// Find the value of a term in the state, which may be the term itself.
    func walk(_ term: Term<Value>) -> Term<Value> {
        if case let .variable(variable) = term, let value = substitution[variable] {
            return walk(value)
        } else if case let .pair(left, right) = term {
            return .pair(walk(left), walk(right))
        } else {
            return term
        }
    }
    
    /// `unify` in µKanren
    /// Attempt to unify two terms in the state--i.e., make them equivalent. If
    /// the terms can't be unified, throws a UnificationError.
    func unify(_ a: Term<Value>, _ b: Term<Value>) throws -> State<Value> {
        let a = walk(a)
        let b = walk(b)
        
        if a == b { return self }
        
        switch (a, b) {
        case let (.variable(a), _):
            return extend(a, b)
        case let (_, .variable(b)):
            return extend(b, a)
        case let (.pair(a1, a2), .pair(b1, b2)):
            return try unify(a1, b1).unify(a2, b2)
        default:
            throw UnificationError()
        }
    }
}

infix operator ≡ : ComparisonPrecedence

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

/// Overload to make comparing variables easier.
func ≡ <Value>(lhs: Variable, rhs: Variable) -> State<Value>.Goal {
    return .variable(lhs) ≡ .variable(rhs)
}

/// Overload to make comparing a variable and a value easier.
func ≡ <Value>(lhs: Variable, rhs: Value) -> State<Value>.Goal {
    return .variable(lhs) ≡ .value(rhs)
}

/// `disj` in µKanren
/// A goal that succeeds when either goal succeeds.
func || <Value>(lhs: State<Value>.Goal, rhs: State<Value>.Goal) -> State<Value>.Goal {
    return { state in lhs(state).interleave(with: rhs(state)) }
}

/// `conj` in µKanren
/// A goal that succeeds when both goals succeed.
func && <Value>(lhs: State<Value>.Goal, rhs: State<Value>.Goal) -> State<Value>.Goal {
    return { state in lhs(state).flatMap(rhs) }
}

/// Introduce a new variable that can be used to create a goal.
func fresh<Value>(block: @escaping (Variable) -> State<Value>.Goal) -> State<Value>.Goal {
    return { state in
        var state = state
        let variable = Variable(index: state.counter)
        state.counter += 1
        return block(variable)(state)
    }
}

/// Introduce two new variables that can be used to create a goal.
func fresh<Value>(block: @escaping (Variable, Variable) -> State<Value>.Goal) -> State<Value>.Goal {
    return fresh { x in fresh { y in { state in block(x, y)(state) } } }
}

/// Introduce three new variables that can be used to create a goal.
func fresh<Value>(block: @escaping (Variable, Variable, Variable) -> State<Value>.Goal) -> State<Value>.Goal {
    return fresh { x in fresh { y in fresh { z in { state in block(x, y, z)(state) } } } }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////

// A goal that demonstrates some basic logic.

let goal1 = fresh { a, b in
    a ≡ 7 && (a ≡ b || b ≡ 6)
}
let iter1 = goal1(State())
iter1.next()
iter1.next()
iter1.next()

////////////////////////////////////////////////////////////////////////////////////////////////////////////////

// A goal that demonstrates that items in lists can be compared.

let goal2 = fresh { x, y, z in
    [.variable(x), .value(4), .variable(z)] ≡ [.value(1), .variable(y), .value(3)]
}
let iter2 = goal2(State())
iter2.next()
iter2.next()

////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/// A goal that tries to combine two lists to equal a third list.
func append<Value>(_ head: Term<Value>, _ tail: Term<Value>, _ list: Term<Value>) -> State<Value>.Goal {
    return (head ≡ .empty && tail ≡ list)
        || fresh { first, restOfHead, restOfList in
            return head ≡ .pair(.variable(first), .variable(restOfHead))
                && list ≡ .pair(.variable(first), .variable(restOfList))
                && append(.variable(restOfHead), tail, .variable(restOfList))
    }
}

// A goal that demostrates append.

let goal3 = fresh { x in
    append([.value("h"), .value("e")], [.value("l"), .value("l"), .value("o")], .variable(x))
}
let iter3 = goal3(State())
iter3.next()
iter3.next()
