import subprocess

# import logging
from flask import Flask, request, send_from_directory

app = Flask(__name__)
app.debug = True

# logfile = ".../racews.log"
prolog_command = [
    "swipl",
    "-x",
    "racews.sav",
    "-g",
    "run_race",
    "-t",
    "halt",
]

@app.route("/")
def index():
    return send_from_directory(".", "racews.html")

@app.route("/service/race", methods=["POST"])
def run_race():
    input_data = request.get_data().decode("utf-8")

    try:
        result = subprocess.run(
            prolog_command, input=input_data, text=True, capture_output=True
        )

        if result.returncode == 0:
            return result.stdout, 200, {"Content-Type": "text/xml"}
        # logging.error("Prolog execution failed: %s", result.stderr)
        return "Error running RACE", 500
    except subprocess.CalledProcessError as _e:
        # logging.error("Prolog execution error: %s", e)
        return "Error running RACE", 500


if __name__ == "__main__":
    app.run()
