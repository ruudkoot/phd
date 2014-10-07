{-# LANGUAGE ViewPatterns #-}

module HTTP (
    RequestType(..),
    URL,
    Version,
    Request(..),
    parseRequest,
    StatusCode,
    ReasonPhrase,
    MessageBody,
    Response(..),
    respond200,
    respond404,
    respond500
) where

import Data.Char

-- | Request

data RequestType = GET | POST
    deriving (Eq, Read, Show)
    
type URL     = String
type Version = String

data Request = Request RequestType URL Version [(String,String)]
    deriving (Show)

parseRequest :: String -> Request
parseRequest (lines . filter (/= '\r') ->
              (words -> [read -> reqType, url, version])
              : (map separate . takeWhile (not . null) -> keyVals)
          ) = Request reqType url version keyVals

separate :: String -> (String, String)
separate (break isSpace -> (init -> key, dropWhile isSpace -> value))
    = (key, value)
    
-- | Response

type StatusCode   = Int
type ReasonPhrase = String
type MessageBody  = String

data Response
    = Response Version StatusCode ReasonPhrase {- headers -} MessageBody

instance Show Response where
    show (Response version statusCode reasonPhrase messageBody)
        = version ++ " " ++ show statusCode ++ " " ++ reasonPhrase ++ "\r\n\r\n"
          ++ messageBody
          
respond200 :: MessageBody -> Response
respond200 = Response "HTTP/1.1" 200 "OK"

respond404 :: Response
respond404 = Response "HTTP/1.1" 404 "Page Not Found"
                      "The requested page does not exist."

respond500 :: Response
respond500 = Response "HTTP/1.1" 500 "Internal Server Error"
                      "An internal server error occurred."
