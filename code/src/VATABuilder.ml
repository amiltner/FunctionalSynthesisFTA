open FTASynthesizer

module VB (*: AutomatonBuilder*) =
  functor (Symbol : Symbol) ->
  functor (State : State) ->
  struct
    module Symbol = Symbol
    module State = State

    type term = Term of Symbol.t * (term list)
  end
