import React from 'react';
// import "../stylesheets/LoginPage.css";
// import "../stylesheets/RegisterPage.css";
// import "../stylesheets/ForgotPasswordPage.css";
import LoginPage from "./Login";
import ResetPasswordPage from "./ResetPassword";
import ForgotPasswordPage from "./ForgotPassword";
import RegisterPage from "./Register";
import HomePage from "./Home";
import { BrowserRouter as Router, Routes, Route } from "react-router-dom";
import AppNavbar from '../components/Navbar/AppNavbar';
import Navbar from '../components/Navbar/Navbar';


export default function App() {
    return (
        <Router>
            <Navbar  />
            <Routes>
                <Route path="/login" element={<LoginPage />} />
                <Route path="/register" element={<RegisterPage />} />
                <Route path="/forgotPassword" element={<ForgotPasswordPage />} />
            </Routes>
        </Router>
    );
}


// import React from 'react';
// import "../stylesheets/HomePage.css";
// // import "../stylesheets/LoginPage.css";
// // import "../stylesheets/RegisterPage.css";
// // import "../stylesheets/ForgotPasswordPage.css";
// // import LoginPage from "./Login";
// // import ResetPasswordPage from "./ResetPassword";
// // import ForgotPasswordPage from "./ForgotPassword";
// // import RegisterPage from "./Register";
// import HomePage from "./Home";
// import { BrowserRouter as Router, Routes, Route } from "react-router-dom";
// import AppNavbar from '../components/Navbar/AppNavbar';
// import Navbar from '../components/Navbar/Navbar';


// export default function App() {
//     return (
//         <Router>
//             <AppNavbar  />
//             <Routes>
//                 {/* <Route path="/login" element={<LoginPage />} />
//                 <Route path="/register" element={<RegisterPage />} />
//                 <Route path="/forgotPassword" element={<ForgotPasswordPage />} /> */}
//                 <Route path="/home" element={<HomePage />} />
//             </Routes>
//         </Router>
//     );
// }