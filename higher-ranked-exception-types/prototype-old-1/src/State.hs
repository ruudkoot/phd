module State (
    State(..),
    initial
) where

data State = State {
    expr :: String
}

initial :: State
initial = State { expr = "" }
