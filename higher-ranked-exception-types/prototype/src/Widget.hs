module Widget where

class Widget w where
    serialize :: w -> String
    deserialize :: String -> w
    render :: w -> String
