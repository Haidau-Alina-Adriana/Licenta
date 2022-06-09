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
            <NavbarLink to="/home"> Home</NavbarLink>
            <NavbarLink to="/predictPrice"> Predict price</NavbarLink>
            <NavbarLink to="/history"> History</NavbarLink>
            <NavbarLink to="/feedback"> Feedback</NavbarLink>
            <NavbarLink to="/logout"> Logout</NavbarLink>
          </NavbarLinkContainer>
        </ContainerTwo>
      </NavbarInnerContainer>
    </NavbarContainer>
  );
}

export default Navbar;
