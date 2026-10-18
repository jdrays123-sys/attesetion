# Attestation Backend

Flask API backend for attestation services.

## Local Development

1. Install dependencies:
```bash
pip install -r requirements.txt
```

2. Run the development server:
```bash
python app.py
```

The server will run on `http://localhost:8080`.

## Deployment to Vercel

1. Initialize a Git repository and push to GitHub:
```bash
git init
git add .
git commit -m "Initial commit"
git remote add origin <your-github-repo-url>
git push -u origin main
```

2. Deploy to Vercel:
- Go to [vercel.com](https://vercel.com) and import your GitHub repository
- Vercel will automatically detect the Python Flask configuration from `vercel.json`
- Deploy!

## Files

- `app.py` - Entry point for Vercel deployment (imports from `latest.py`)
- `latest.py` - Main Flask application
- `vercel.json` - Vercel deployment configuration
- `requirements.txt` - Python dependencies (including gunicorn for production)
