import React, { useState } from 'react';
import "../stylesheets/RegisterPage.css";

function RegisterPage({ error }) {
    const [details, setDetails] = useState({ email: "", password: "" });
    // const [error, setError] = useState({error: ""})

    // const submitHandler = e => {
    //     e.preventDefault();
    //     Register(details);
    // }
    return (
        // <form onSubmit={submitHandler}>
        <div className="App">
        <form>
            <div className='container-register'>
                <div className='register-info box2'>

                    <div className='info'>
                        <h3>Fruits price prediction</h3>
                        <p>“Peace, love, and pineapples.” — Unknown</p>
                    </div>
                    <div className='container-fruits'>
                        <div className='peach'></div>
                        <div className='avocado'></div>
                        <div className='blueberry'></div>
                        <div className='kiwi'></div>
                        <div className='strawberry'></div>
                    </div>
                </div>
                <div className="register-info">
                    <div className='logo-image' />
                    <h2>Getting started</h2>
                    <div className="register-form">
                        <label htmlFor='email'>Email</label>
                        <input type="text" name="email" id="email" onChange={e => setDetails({ ...details, email: e.target.value })} value={details.email} />
                    </div>

                    <div className="register-form">
                        <label htmlFor='password'>Password</label>
                        <input type="password" name="password" id="password" onChange={e => setDetails({ ...details, password: e.target.value })} value={details.password} />
                    </div>

                    <div className="register-form">
                        <label htmlFor='password'>Confirm Password</label>
                        <input type="password" name="password" id="cpassword" onChange={e => setDetails({ ...details, password: e.target.value })} value={details.password} />
                    </div>


                    <input type="submit" value="Register" />

                    {(error !== "") ? (<div className='error'>{error}</div>) : (<div className='error2'>No error</div>)}

                    <div className='register-with-other-apps'>
                        <h5><span>Or register with</span></h5>
                        <div className='container-apps'>
                            <button className='google-register' type='submit'></button>
                            <button className='facebook-register' type='submit'></button>
                        </div>
                    </div>
                </div>

            </div>
        </form>
        </div>
    )
}

export default RegisterPage;