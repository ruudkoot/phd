module Page.Main (
    render
) where

render :: IO String
render = return $ unlines [
    "<!DOCTYPE html>",
    "<html lang=\"en\">",
        "<head>",
            "<meta charset=\"utf-8\">",
            "<meta http-equiv=\"X-UA-Compatible\" content=\"IE=edge\">",
            "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">",
            "<title>Big Data in the Cloud-as-a-service</title>",
            "<link rel=\"stylesheet\" href=\"http://localhost:8666/static/bootstrap/3.1.1/css/bootstrap.min.css\">",
            "<link rel=\"stylesheet\" href=\"http://localhost:8666/static/bootstrap/3.1.1/css/bootstrap-theme.min.css\">",
            "<script type=\"text/javascript\" src=\"http://localhost:8666/static/mathjax/MathJax.js\"></script>",
        "</head>",
        "<body>",
            "<h1>Title</h1>",
            "<p>Lorum ipsum dolor sit amet</p>",
            "<script src=\"http://localhost:8666/static/jquery/1.11.0/jquery.js\"></script>",
            "<script src=\"http://localhost:8666/static/bootstrap/3.1.1/js/bootstrap.min.js\"></script>",
        "</body>",
    "</html>"
  ]
