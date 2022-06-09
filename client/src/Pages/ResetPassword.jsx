import React, { useState } from 'react';
import "../stylesheets/ResetPasswordPage.css";

function ForgotPasswordPage({ error }) {

    const [details, setDetails] = useState({ email: "", password: "" });

    return (
        <div className="App">
            <form>
                <div className='container-reset-password'>
                    <div className="reset-password-info">
                        <div className='logo-image' />
                        <div className='back'>Back to login</div>
                        <h2 className='title'>Reset password</h2>
                        <div className='reset-password'>
                            <p>Please choose a new password.
                            </p>
                        </div>
                        <div className="reset-password-form">
                            <label htmlFor='password'>Password</label>
                            <input type="password" name="password" id="password" onChange={e => setDetails({ ...details, password: e.target.value })} value={details.password} />
                        </div>

                        <div className="reset-password-form">
                            <label htmlFor='password'>Confirm Password</label>
                            <input type="password" name="cpassword" id="cpassword" onChange={e => setDetails({ ...details, cpassword: e.target.value })} value={details.cpassword} />
                        </div>

                        <input type="submit" value="Change password" />

                        {(error !== "") ? (<div className='error'>{error}</div>) : (<div className='error2'>No error</div>)}


                    </div>
                    <div className='reset-password-info box2'>
                    </div>
                </div>
            </form>
        </div>
    )
}

export default ForgotPasswordPage;