import React from 'react'
import { NavbarContainer,
  ContainerTwo,
  NavbarInnerContainer,
  NavbarLinkContainer,
  NavbarLink,
} from "./NavbarElements"


function Navbar() {

  return (
    <NavbarContainer>
      <NavbarInnerContainer>
        <ContainerTwo>
          <NavbarLinkContainer>
            <NavbarLink to="/login"> Login</NavbarLink>
            <NavbarLink to="/register"> Register</NavbarLink>
            <NavbarLink to="/forgotPassword"> Forgot Password</NavbarLink>
          </NavbarLinkContainer>
        </ContainerTwo>
      </NavbarInnerContainer>
    </NavbarContainer>
  );
}

export default Navbar;
