from flask import Blueprint, render_template
from flask_login import login_required, current_user

main = Blueprint('main', __name__)

@main.route('/home')
@login_required
def home():
    return render_template('home.html', email=current_user.email)

@main.route('/predict_price')
@login_required
def predict_price():
    return render_template('predict_price.html', email=current_user.email)

@main.route('/feedback')
@login_required
def feedback():
    return render_template('feedback.html', email=current_user.email)

@main.route('/history')
@login_required
def history():
    return render_template('history.html', email=current_user.email)