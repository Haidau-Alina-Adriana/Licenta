import styled from "styled-components";
import { Link } from "react-router-dom";

export const NavbarContainer = styled.nav`
  width: 100%;
  height: ${(props) => (props.extendNavbar ? "95vh" : "72px")};
  background-color:#00d1b2;
  display: flex;
  flex-direction: column;

`;

export const ContainerOne = styled.div`
  flex: 70%;
  display: flex;
  padding-left: 5%;
`;

export const ContainerTwo = styled.div`
  flex: 30%;
  display: flex;
  justify-content: flex-end;
  align-items: center;
  padding-right: 4em;
`;

export const NavbarInnerContainer = styled.div`
  width: 100%;
  height: 80px;
  display: flex;
`;

export const NavbarLinkContainer = styled.div`
  display: flex;
`;

export const NavbarLink = styled(Link)`
  color: #ffffff;
  font-size: medium;
  /* font-weight: bold; */
  font-family: sans-serif;
  text-decoration: none;
  margin: 0 20px;
  &:hover {
    color: rgba(86, 59, 59, 0.2);
  } 
`;

export const Logo = styled.img`
  margin: 10px;
  max-width: 180px;
  height: auto;
`;