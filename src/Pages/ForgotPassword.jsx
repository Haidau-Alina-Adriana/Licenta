import React, { useState } from 'react';
import "../stylesheets/ForgotPasswordPage.css";

function ForgotPasswordPage({ error }) {

    const [details, setDetails] = useState({ email: "", password: "" });

    return (
        <div className="App">
            <form>
                <div className='container-forgot-password'>
                    <div className="forgot-password-info">
                        <div className='logo-image' />
                        <div className='back'>Back to login</div>
                        <h2 className='title'>Forgot password</h2>
                        <div className='forgot-password'>
                            <p>Send a link to your email to reset your password.
                            </p>
                        </div>
                        <div className="forgot-password-form">
                            <label htmlFor='email'>Email</label>
                            <input type="text" name="email" id="email" onChange={e => setDetails({ ...details, email: e.target.value })} value={details.email} />
                        </div>


                        <input type="submit" value="Send reset link " />

                        {(error !== "") ? (<div className='error'>{error}</div>) : (<div className='error2'>No error</div>)}


                    </div>
                    <div className='forgot-password-info box2'>

                        <div className='info'>
                        </div>
                    </div>
                </div>
            </form>
        </div>
    )
}

export default ForgotPasswordPage;