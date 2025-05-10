from openai import OpenAI
import sys

# Ask the user for input
user_input = input("What is your request?\n")

# Load the prompt template from 'prompt.txt'
with open("prompt.txt", "r") as file:
    prompt_template = file.read()

# Replace the placeholder with the actual user input
modified_prompt = prompt_template.replace("PLEASE REPLACE WITH USER REQUEST", user_input)

# Initialize OpenAI client
client = OpenAI()

# Send the request to the API
response = client.responses.create(
    model="o3-mini",
    input=[
        {
            "role": "user",
            "content": [
                {
                    "type": "input_text",
                    "text": modified_prompt
                }
            ]
        }
    ],
    text={
        "format": {
            "type": "text"
        }
    },
    reasoning={
        "effort": "medium"
    },
    tools=[],
    store=True
)

# Print the response
print(response.output[1].content[0].text)
