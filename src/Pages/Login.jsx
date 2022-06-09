import React, { useState } from 'react';
import "../stylesheets/LoginPage.css";

function LoginPage({error}) {
    const [details, setDetails] = useState({ email: "", password: "" });

    return (
        <div className="App">
            <form action="#" method='POST'>
                <div className='container-login'>
                    <div className="login-info">
                        <div className='logo-image' />
                        <h2>Login</h2>
                        <div className="login-form">
                            <label htmlFor='email'>Email</label>
                            <input type="text" name="email" id="email" onChange={e => setDetails({ ...details, email: e.target.value })} value={details.email} />
                        </div>

                        <div className="login-form">
                            <label htmlFor='password'>Password</label>
                            <input type="password" name="password" id="password" onChange={e => setDetails({ ...details, password: e.target.value })} value={details.password} />

                        </div>

                        <input type="submit" value="LOGIN" />

                        {(error !== "") ? (<div className='error'>{error}</div>) : (<div className='error2'>No error</div>)}

                        <div className='login-with-other-apps'>
                            <h5><span>Or login with</span></h5>
                            <div className='container-apps'>
                                <button className='google-login' type='submit'></button>
                                <button className='facebook-login' type='submit'></button>
                            </div>
                        </div>
                    </div>
                    <div className='login-info box2'>

                        <div className='info'>
                            <h3>Fruits price prediction</h3>
                            <p> Health is the most important quality you can have!</p>
                        </div>
                        <div className='container-fruits'>
                            <div className='peach'></div>
                            <div className='avocado'></div>
                            <div className='blueberry'></div>
                            <div className='kiwi'></div>
                            <div className='strawberry'></div>
                        </div>
                    </div>
                </div>
            </form>
            </div>
    )
}

export default LoginPage;