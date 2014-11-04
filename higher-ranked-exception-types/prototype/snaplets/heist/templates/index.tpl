<apply template="base">

  <ifLoggedIn>
    <p>Welcome <loggedInUser/>. (<a href="/logout">Logout</a>)</p>

    <ul>
      <li><a href="/lambda-union">lambda-union</a></li>
    </ul>

  </ifLoggedIn>

  <ifLoggedOut>
    <apply template="_login"/>
  </ifLoggedOut>

</apply>
